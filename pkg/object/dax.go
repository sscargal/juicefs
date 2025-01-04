//go:build !nodax
// +build !nodax

package object

import (
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/juicedata/juicefs/pkg/meta" // Import the meta package
	"golang.org/x/sys/unix"
)

// Compile-time check to ensure *daxStore implements ObjectStorage.
var _ ObjectStorage = (*daxStore)(nil)

// Ensure daxStore implements the meta.Meta interface
var _ meta.Meta = (*daxStore)(nil)

const (
	// defaultPageSize is the size of a memory page.
	// We use 4KiB (common) by default, but this could be another supported page size (2MiB, 1GiB, etc).
	defaultPageSize = 4096

	// daxHeaderSize is the size of the header in bytes (2MiB).
	headerSize = 2 * 1024 * 1024 // 2MiB

	// We'll store this Magic number at the start of the DAX region.
	// This helps us identify the region as a DAX device managed by JuiceFS
	// 0x4441584653 =="DAXFS" in ASCII:
	daxMagic uint64 = 0x4441584653
)

// daxHeader defines metadata stored at the start of the DAX device.
type daxHeader struct {
	Magic       uint64   // must match daxMagic
	Version     uint32   // the on-disk format version
	TotalSize   int64    // total size of the device
	FreeListOff int64    // where the free list/bitmap starts (in bytes)
	FreeListLen int64    // length of the free list structure
	Checksum    [32]byte // 32 bytes (SHA-256) checksum of the object data
	// TODO: Add more fields (checksum, last mount time, etc.)
}

// daxStore is our driver struct that implements the ObjectStorage interface.
// It manages the /dev/dax* device(s), the in-memory metadata index, and a simple
// SLAB allocator for storing object data in persistent memory via mmap.
type daxStore struct {
	metaMu               sync.RWMutex          // protects objectIndex
	DefaultObjectStorage                       // embed the default implementation
	name                 string                // name of the DAX store
	devPath              string                // path to /dev/daxX.Y
	size                 int64                 // size (in bytes) of the DAX device
	data                 []byte                // memory-mapped data from the DAX device
	fd                   int                   // file descriptor of the DAX device
	objectIndex          map[string]*daxObject // metadata: keys -> object info

	// Allocator
	alloc  *allocator // our simple SLAB allocator for pages
	header *daxHeader // header metadata

	// hdrLock protects access to the header and free list.
	// Always acquire hdrLock before modifying header or free list.
	hdrLock sync.Mutex
}

// daxObject holds metadata for a single object stored in the daxStore.
// This includes SLAB allocations, size, and other attributes.
type daxObject struct {
	key        string      // object key
	size       int64       // object size in bytes
	checksum   [32]byte    // SHA-256 checksum of the object data
	pageRanges []pageRange // one or multiple allocated page ranges
}

// pageRange holds the start and length of pages allocated in the device
// that store the data for an object.
type pageRange struct {
	startPage int64 // starting page number
	numPages  int64 // number of pages in this range
}

// allocator is our simplistic SLAB allocator that tracks allocated and free pages.
type allocator struct {
	totalPages int64       // total number of pages in the device
	pageMu     sync.Mutex  // protects freeList
	freeList   []freeBlock // list of free blocks
}

// freeBlock describes a contiguous range of free pages.
type freeBlock struct {
	startPage int64 // starting page number
	numPages  int64 // number of pages in this block
}

// newDaxStore is a convenience constructor. It creates a new DAX store instance with a persistent header (label).
// The device is memory-mapped and the header is loaded (or initialized if new).
// The free list is also loaded (or initialized if new).
// The store is returned with the header and free list in memory.
func newDaxStore(endpoint, accessKey, secretKey, token string) (ObjectStorage, error) {
	logger.Debugf("newDaxStore(): endpoint='%s', accessKey='%s', secretKey='%s', token='%s'", endpoint, accessKey, secretKey, token)

	// Strip the "dax://" prefix and any trailing slash to get "/dev/dax0.0"
	if !strings.HasPrefix(endpoint, "dax://") {
		return nil, fmt.Errorf("invalid endpoint for dax driver: %s", endpoint)
	}
	devPath := strings.TrimPrefix(endpoint, "dax://")
	devPath = strings.TrimSuffix(devPath, "/")
	if devPath == "" {
		return nil, errors.New("device path is empty")
	}

	// Validate /dev/dax*
	// Returns 'daxX.Y' or an error if the path is invalid from '/dev/dax/X.Y'
	base, err := extractDaxName(devPath)
	if err != nil {
		return nil, err
	}

	// Get the DevDax device size from sysfs
	sz, err := readDaxSize(base)
	if err != nil {
		return nil, err
	}

	// Open the dax device
	fd, err := unix.Open(devPath, unix.O_RDWR, 0)
	if err != nil {
		return nil, fmt.Errorf("failed to open dax device: %w", err)
	}

	// Ensure the device is large enough to hold the header
	if sz < headerSize {
		unix.Close(fd)
		return nil, fmt.Errorf("DAX device '%s' is too small (size = %d bytes); need >= %d bytes",
			devPath, sz, headerSize)
	}

	// Memory map the dax device
	data, err := unix.Mmap(fd, 0, int(sz), unix.PROT_READ|unix.PROT_WRITE, unix.MAP_SHARED)
	if err != nil {
		_ = unix.Close(fd)
		return nil, fmt.Errorf("failed to mmap dax device: %w", err)
	}
	// Ensure the memory mapped dax device has enough capacity for the header
	if len(data) < headerSize {
		_ = unix.Munmap(data)
		_ = unix.Close(fd)
		return nil, fmt.Errorf("mapped data is only %d bytes, expected >= %d", len(data), headerSize)
	}
	logger.Debugf("Mapped size = %d, got ds.data length = %d", sz, len(data))

	// Build our store instance
	ds := &daxStore{
		name:        base,                        // Store the dax base name as the store name (e.g., "dax0.0")
		devPath:     devPath,                     // Store the device path (e.g., "/dev/dax0.0")
		size:        sz,                          // Store the size of the device in bytes
		data:        data,                        // Store the memory-mapped data
		fd:          fd,                          // Store the file descriptor
		objectIndex: make(map[string]*daxObject), // Initialize the object index
	}

	if err := ds.loadHeaderAndAlloc(); err != nil {
		// If load fails, unmap and close
		_ = unix.Munmap(data)
		_ = unix.Close(fd)
		return nil, fmt.Errorf("failed to load header: %w", err)
	}

	return ds, nil
}

// loadHeaderAndAlloc loads (or creates) the daxHeader at offset 0,
// then loads (or initializes) the free list data structure.
func (ds *daxStore) loadHeaderAndAlloc() error {
	if ds.size < headerSize {
		return fmt.Errorf("DAX device size too small (size = %d), cannot hold header", ds.size)
	}

	hdr := &daxHeader{}
	headerBuf := ds.data[0:headerSize]

	// Read the magic number first (4 bytes).
	rawMagic := binary.LittleEndian.Uint32(headerBuf[0:8])
	hdr.Magic = uint64(rawMagic)

	// Compare the magic number to determine if this is a fresh or invalid (must create a new one)
	// or an existing header (with existing data).
	if hdr.Magic != daxMagic {
		// Fresh or invalid header => Initialize.
		logger.Debugf("Initializing new header")
		hdr.Magic = daxMagic
		hdr.Version = 1
		hdr.TotalSize = int64(len(ds.data))
		hdr.FreeListOff = headerSize
		hdr.FreeListLen = 0 // set later when we write a free list

		// Acquire hdrLock before writing the header
		ds.hdrLock.Lock()
		defer ds.hdrLock.Unlock()

		// Write the freshly initialized header to the device
		if err := ds.writeHeader(hdr); err != nil {
			return err
		}

		// Build a brand-new free list in memory (everything is free)
		// The startPage must start after the header (headerSize) + 1 to avoid corrupting the header
		// The total number of allocatable/available pages is reduced by the number of pages needed for the header.
		startOffsetPg := pagesNeeded(headerSize + 1)
		ds.alloc = &allocator{
			totalPages: hdr.TotalSize / defaultPageSize,
			freeList: []freeBlock{
				{startPage: startOffsetPg, numPages: (hdr.TotalSize / defaultPageSize) - startOffsetPg},
			},
		}
	} else {
		// Existing header => read the rest of the fields.
		hdr.Version = binary.LittleEndian.Uint32(headerBuf[8:12])
		hdr.TotalSize = int64(binary.LittleEndian.Uint64(headerBuf[12:20]))
		hdr.FreeListOff = int64(binary.LittleEndian.Uint64(headerBuf[20:28]))
		hdr.FreeListLen = int64(binary.LittleEndian.Uint64(headerBuf[28:36]))

		// Read and verify the checksum
		var storedChecksum [32]byte
		copy(storedChecksum[:], headerBuf[36:68])

		// Compute checksum over the first 36 bytes
		computedChecksum := sha256.Sum256(headerBuf[0:36])

		logger.Debugf("Verifying checksum: stored=%x, computed=%x", storedChecksum, computedChecksum)

		if storedChecksum != computedChecksum {
			return fmt.Errorf("checksum mismatch: stored %x, computed %x", storedChecksum, computedChecksum)
		}

		logger.Debugf("Read existing header: Magic=%x, Version=%d, TotalSize=%d, FreeListOff=%d, FreeListLen=%d",
			hdr.Magic, hdr.Version, hdr.TotalSize, hdr.FreeListOff, hdr.FreeListLen)

		logger.Debugf("The header is valid! Loading free list")

		ds.alloc = &allocator{
			totalPages: hdr.TotalSize / defaultPageSize,
			freeList:   make([]freeBlock, 0),
		}

		// If FreeListLen is nonzero, parse the free list from [FreeListOff .. FreeListOff+FreeListLen].
		freeListData := ds.data[hdr.FreeListOff : hdr.FreeListOff+hdr.FreeListLen]
		for offset := 0; offset+16 <= len(freeListData); offset += 16 {
			startPg := int64(binary.LittleEndian.Uint64(freeListData[offset : offset+8]))
			numPgs := int64(binary.LittleEndian.Uint64(freeListData[offset+8 : offset+16]))
			ds.alloc.freeList = append(ds.alloc.freeList, freeBlock{
				startPage: startPg,
				numPages:  numPgs,
			})
		}

		logger.Debugf("Loaded %d free blocks from free list", len(ds.alloc.freeList))
	}

	ds.header = hdr
	return nil
}

// writeHeader writes the given daxHeader to the start of the mapped device.
func (ds *daxStore) writeHeader(hdr *daxHeader) error {
	// Found a deadlock with persistFreeList() if we lock here.
	// ds.hdrLock.Lock()
	// defer ds.hdrLock.Unlock()

	buf := make([]byte, headerSize)
	// Write fields in little-endian order
	binary.LittleEndian.PutUint64(buf[0:8], hdr.Magic)                 // [0..8]: Magic (64 bits)
	binary.LittleEndian.PutUint32(buf[8:12], hdr.Version)              // [8..12]: Version (32 bits)
	binary.LittleEndian.PutUint64(buf[12:20], uint64(hdr.TotalSize))   // [12..20]: TotalSize (64 bits)
	binary.LittleEndian.PutUint64(buf[20:28], uint64(hdr.FreeListOff)) // [20..28]: FreeListOff (64 bits)
	binary.LittleEndian.PutUint64(buf[28:36], uint64(hdr.FreeListLen)) // [28..36]: FreeListLen (64 bits)

	// Compute checksum over the first 36 bytes
	checksum := sha256.Sum256(buf[0:36])
	copy(buf[36:68], checksum[:]) // [36..68]: Checksum (32 bytes)

	logger.Debugf("Writing header: Magic=%x, Version=%d, TotalSize=%d, FreeListOff=%d, FreeListLen=%d, Checksum=%x",
		hdr.Magic, hdr.Version, hdr.TotalSize, hdr.FreeListOff, hdr.FreeListLen, checksum)

	// Copy the buffer to the mapped memory
	copy(ds.data[0:headerSize], buf)

	return nil
}

// persistFreeList writes the free list from ds.alloc into the device
// at [header.FreeListOff .. header.FreeListOff + N], and updates the header’s FreeListLen.
func (ds *daxStore) persistFreeList() error {
	ds.hdrLock.Lock()
	defer ds.hdrLock.Unlock()

	// Each storedFreeBlock is 16 bytes (two int64).
	blockSize := 16
	required := len(ds.alloc.freeList) * blockSize
	if ds.header.FreeListOff+int64(required) > int64(len(ds.data)) {
		return errors.New("not enough space to store free list (device too small?)")
	}

	// Build a buffer
	flData := make([]byte, required)
	offset := 0
	for _, fb := range ds.alloc.freeList {
		binary.LittleEndian.PutUint64(flData[offset:offset+8], uint64(fb.startPage))
		binary.LittleEndian.PutUint64(flData[offset+8:offset+16], uint64(fb.numPages))
		offset += 16
	}

	// Copy to mapped memory
	copy(ds.data[ds.header.FreeListOff:ds.header.FreeListOff+int64(required)], flData)

	// Update header
	ds.header.FreeListLen = int64(required)
	if err := ds.writeHeader(ds.header); err != nil {
		return err
	}

	return nil
}

// -------------------------------------
//  Private Helpers
// -------------------------------------

// extractDaxName extracts the DAX device name from the device path.
// It returns the device name or an error if the path is invalid.
// For example, "/dev/dax0.0" would return "dax0.0".
func extractDaxName(devPath string) (string, error) {
	logger.Debugf("extractDaxName(): devPath='%s'", devPath)
	base := filepath.Base(devPath)
	if !strings.HasPrefix(base, "dax") {
		return "", fmt.Errorf("not a dax device: %s", base)
	}
	logger.Debugf("extractDaxName(): base='%s'", base)
	return base, nil
}

// readDaxSize reads the size of the DAX device from sysfs.
// It returns the size in bytes or an error if the size cannot be read.
func readDaxSize(daxName string) (int64, error) {
	logger.Debugf("readDaxSize(): daxName='%s'", daxName)
	sysfsPath := filepath.Join("/sys/bus/dax/devices/", daxName, "/size")
	logger.Debugf("readDaxSize(): sysfsPath='%s'", sysfsPath)
	f, err := os.Open(sysfsPath)
	if err != nil {
		return 0, fmt.Errorf("readDaxSize(): open sysfs: %w", err)
	}
	defer f.Close()

	r := bufio.NewReader(f)
	line, err := r.ReadString('\n')
	if err != nil && err != io.EOF {
		return 0, fmt.Errorf("readDaxSize(): read sysfs: %w", err)
	}
	line = strings.TrimSpace(line)
	sz, convErr := strconv.ParseInt(line, 10, 64)
	if convErr != nil {
		return 0, fmt.Errorf("readDaxSize(): invalid size in sysfs: %w", convErr)
	}
	logger.Debugf("readDaxSize(): size=%d", sz)
	return sz, nil
}

// pagesNeeded calculates the number of pages needed to store `size` bytes.
// It rounds up to the nearest page size.
func pagesNeeded(size int64) int64 {
	if size <= 0 {
		return 0
	}
	return (size + defaultPageSize - 1) / defaultPageSize
}

// -------------------------------------
//  Allocator Functions
// -------------------------------------

// allocatePages finds a contiguous range of pages that can hold `numPages` pages.
// It returns the starting page number or an error if there's not enough space.
func (a *allocator) allocatePages(numPages int64) (int64, error) {
	a.pageMu.Lock()
	defer a.pageMu.Unlock()

	logger.Debugf("allocatePages(): allocating numPages=%d", numPages)

	for i, block := range a.freeList {
		if block.numPages >= numPages {
			// allocate from this block
			allocStart := block.startPage
			remaining := block.numPages - numPages
			// update the freeBlock
			block.startPage += numPages
			block.numPages = remaining

			// if we used up the entire block, remove it
			if block.numPages == 0 {
				a.freeList = append(a.freeList[:i], a.freeList[i+1:]...)
			} else {
				a.freeList[i] = block
			}
			return allocStart, nil
		}
	}

	return 0, errors.New("insufficient space in DAX device")
}

// freePages frees a contiguous range of pages. It merges with adjacent free blocks when possible.
// The `startPage` is the starting page number and `numPages` is the number of pages to free.
// This function assumes that the caller has already locked the allocator.
// It does not return an error because freeing pages should always succeed.
func (a *allocator) freePages(startPage, numPages int64) {
	a.pageMu.Lock()
	defer a.pageMu.Unlock()

	logger.Debugf("freePages(): freeing startPage=%d, numPages=%d", startPage, numPages)

	// endPage := startPage + numPages
	insertIdx := 0

	// Find the correct insertion point to maintain sorted order
	for i, block := range a.freeList {
		if block.startPage >= startPage {
			insertIdx = i
			break
		}
		insertIdx = i + 1
	}

	// Insert a new freeBlock
	newBlock := freeBlock{startPage: startPage, numPages: numPages}
	a.freeList = append(a.freeList, freeBlock{})           // expand slice
	copy(a.freeList[insertIdx+1:], a.freeList[insertIdx:]) // shift
	a.freeList[insertIdx] = newBlock

	// Attempt to merge with previous block
	if insertIdx > 0 {
		prevBlock := a.freeList[insertIdx-1]
		if prevBlock.startPage+prevBlock.numPages == startPage {
			// merge
			a.freeList[insertIdx-1].numPages += newBlock.numPages
			// remove inserted block
			a.freeList = append(a.freeList[:insertIdx], a.freeList[insertIdx+1:]...)
			insertIdx--
			newBlock = a.freeList[insertIdx]
		}
	}

	// Attempt to merge with next block
	if insertIdx < len(a.freeList)-1 {
		nextBlock := a.freeList[insertIdx+1]
		if newBlock.startPage+newBlock.numPages == nextBlock.startPage {
			// merge
			a.freeList[insertIdx].numPages += nextBlock.numPages
			a.freeList = append(a.freeList[:insertIdx+1], a.freeList[insertIdx+2:]...)
		}
	}
}

// -------------------------------------
//  Implement ObjectStorage interface
// -------------------------------------

// Returns a user-friendly name of the storage driver.
func (ds *daxStore) String() string {
	return fmt.Sprintf("dax://%s/", ds.name)
}

// Limits returns the capabilities or limitations of this storage driver.
// This includes the minimum and maximum part sizes for multipart uploads (if supported).
func (ds *daxStore) Limits() Limits {
	// TODO: Adjust these to reflect real capabilities.
	return Limits{
		// No inherent limit for object size (other than the size of the storage device)
		MinPartSize: 0,       // minimum part size for multipart uploads
		MaxPartSize: ds.size, // maximum part size for multipart uploads
	}
}

// Create is typically used to ensure the underlying storage container/bucket
// is created. For DAX, there's not much to do; the device is "created" externally.
// This method is a no-op.
func (ds *daxStore) Create() error {
	// For demonstration, no real "create" logic is required since the device
	// is already present. We could format the region or zero it out if needed.
	return nil
}

// Head returns the metadata for an object without fetching its data.
// It returns an error if the object does not exist.
func (ds *daxStore) Head(key string) (Object, error) {
	ds.metaMu.RLock()
	defer ds.metaMu.RUnlock()

	obj, found := ds.objectIndex[key]
	if !found {
		logger.Debugf("Head(): key=%s not found", key)
		return nil, os.ErrNotExist
	}
	return &objWrap{key: obj.key, size: obj.size}, nil
}

// Get retrieves an object's data by reading from the allocated pages in the DAX device.
func (ds *daxStore) Get(key string, off, limit int64, getters ...AttrGetter) (io.ReadCloser, error) {
	// Grab a read lock on the metadata
	ds.metaMu.RLock()
	defer ds.metaMu.RUnlock()

	// Find the object in the index
	obj, found := ds.objectIndex[key]
	if !found {
		return nil, os.ErrNotExist
	}
	// Check for valid offset and limit
	if off < 0 || off >= obj.size {
		return nil, io.EOF
	}
	// If limit is zero or negative, read the entire object
	if limit <= 0 || off+limit > obj.size {
		limit = obj.size - off
	}

	// We'll read from the relevant pages in sequence
	dataBuf := make([]byte, 0, limit)
	bytesLeft := limit
	bytesToSkip := off
	for _, pr := range obj.pageRanges {
		// Compute the chunk size for this page range
		chunkSize := pr.numPages * defaultPageSize
		// If there's no overlap with (off -> off+limit), skip or partial
		rangeStartByte := pr.startPage * defaultPageSize
		// rangeEndByte := rangeStartByte + chunkSize

		// If skip region is beyond this block, skip
		if bytesToSkip >= chunkSize {
			bytesToSkip -= chunkSize
			continue
		}

		// find how many bytes to read from this block
		readStart := rangeStartByte + bytesToSkip
		readLen := chunkSize - bytesToSkip
		if readLen > bytesLeft {
			readLen = bytesLeft
		}

		dataBuf = append(dataBuf, ds.data[readStart:readStart+readLen]...)
		bytesLeft -= readLen
		bytesToSkip = 0 // we've consumed the skip in this block

		if bytesLeft == 0 {
			break
		}
	}

	// Compute the SHA-256 checksum of the read data
	computedHash := sha256.Sum256(dataBuf)

	// Compare the computed checksum with the stored checksum in the daxObject.checksum
	if computedHash != obj.checksum {
		// Log detailed information for debugging
		logger.Errorf("Get: Checksum mismatch for key %s", key)
		logger.Errorf("Get: Expected SHA256: %x", obj.checksum)
		logger.Errorf("Get: Computed SHA256: %x", computedHash)
		return nil, fmt.Errorf("checksum mismatch for key %s", key)
	}

	// If checksum verification passes, proceed to return the data
	r := bytes.NewReader(dataBuf)
	rc := io.NopCloser(r)
	return rc, nil
}

// Put writes the entire content of `in` as a new or overwritten object.
func (ds *daxStore) Put(key string, in io.Reader, getters ...AttrGetter) error {
	// Read all data from 'in' into a buffer
	data, err := io.ReadAll(in)
	if err != nil {
		return fmt.Errorf("Put(): failed to read data: %w", err)
	}
	size := int64(len(data))

	// Calculate pages needed
	pages := pagesNeeded(size)

	// Allocate pages
	allocStart, err := ds.alloc.allocatePages(pages)
	if err != nil {
		return fmt.Errorf("allocation error: %w", err)
	}

	logger.Debugf("Put(): key=%s, size=%d, pagesNeeded=%d, startPage=%d", key, size, pages, allocStart)

	// Compute SHA-256 checksum of the data to be written
	writeHash := sha256.Sum256(data)
	logger.Debugf("Put: Computed write SHA256 for key=%s: %s", key, hex.EncodeToString(writeHash[:]))

	// Write data to the allocated pages
	pageOffset := allocStart * defaultPageSize

	// Ensure pageOffset is after the header
	if pageOffset < headerSize {
		logger.Debugf("Put: Attempting to write data within header region; pageOffset=%d, headerSize=%d", pageOffset, headerSize)
		return fmt.Errorf("Put: Attempting to write data within header region; pageOffset=%d, headerSize=%d", pageOffset, headerSize)
	}
	copy(ds.data[pageOffset:pageOffset+size], data)
	logger.Debugf("Put: Wrote data for key=%s at offset=%d, size=%d", key, pageOffset, len(data))

	// DEBUG Read back the data immediately for verification
	// readBack := ds.data[pageOffset : pageOffset+size]
	// logger.Debugf("Put: Read back data for key=%s from offset=%d, size=%d: %x", key, pageOffset, len(data), readBack)

	// DEBUG Compute SHA-256 checksum of the read data
	// readHash := sha256.Sum256(readBack)
	// logger.Debugf("Put: Computed read SHA256 for key=%s: %s", key, hex.EncodeToString(readHash[:]))

	// Verify checksum
	// if writeHash != readHash {
	//	logger.Debugf("Put: Checksum mismatch after write for key %s", key)
	//	logger.Debugf("Put: Write SHA256: %s", hex.EncodeToString(writeHash[:]))
	//	logger.Debugf("Put: Read SHA256: %s", hex.EncodeToString(readHash[:]))
	//	return fmt.Errorf("checksum mismatch after write for key %s", key)
	// }

	// logger.Debugf("Put: Data and checksum verified successfully for key %s", key)

	// Update metadata: free old pages if the key already exists
	ds.metaMu.Lock()
	oldObj, found := ds.objectIndex[key]
	if found {
		for _, pr := range oldObj.pageRanges {
			ds.alloc.freePages(pr.startPage, pr.numPages)
		}
		// Since we changed the free list by freeing pages, persist it
		if err := ds.persistFreeList(); err != nil {
			ds.metaMu.Unlock()
			return fmt.Errorf("Put(): persist free list after freeing old pages: %w", err)
		}
	}

	ds.objectIndex[key] = &daxObject{
		key:      key,
		size:     size,
		checksum: writeHash,
		pageRanges: []pageRange{
			{startPage: allocStart, numPages: pages},
		},
	}
	ds.metaMu.Unlock()

	// Persist the free list changes once the new allocation is in place
	if err := ds.persistFreeList(); err != nil {
		return fmt.Errorf("Put(): persist free list after Put: %w", err)
	}

	return nil
}

// Copy duplicates the object from src to dst within the DAX store.
func (ds *daxStore) Copy(dst, src string) error {
	ds.metaMu.RLock()
	obj, found := ds.objectIndex[src]
	ds.metaMu.RUnlock()
	if !found {
		logger.Debugf("Copy(): src=%s not found", src)
		return os.ErrNotExist
	}

	// Read data from src
	r, err := ds.Get(src, 0, obj.size)
	if err != nil {
		logger.Debugf("Copy(): Get error: %v", err)
		return err
	}
	defer r.Close()
	data, err := io.ReadAll(r)
	if err != nil {
		logger.Debugf("Copy(): ReadAll error: %v", err)
		return err
	}

	// Put data into dst (Put will persist free list as needed)
	return ds.Put(dst, bytes.NewReader(data))
}

// Delete removes an object's metadata and frees the allocated pages.
func (ds *daxStore) Delete(key string, getters ...AttrGetter) error {
	ds.metaMu.Lock()
	defer ds.metaMu.Unlock()

	obj, found := ds.objectIndex[key]
	if !found {
		// Key not found; nothing to delete
		return nil
	}

	// Free the pages used by this object
	for _, pr := range obj.pageRanges {
		ds.alloc.freePages(pr.startPage, pr.numPages)
	}
	delete(ds.objectIndex, key)

	// Persist changes to the free list
	if err := ds.persistFreeList(); err != nil {
		return fmt.Errorf("Delete(): persist free list after Delete: %w", err)
	}

	return nil
}

// List returns a slice of objects for the prefix, plus info about truncated results.
func (ds *daxStore) List(prefix, startAfter, token, delimiter string, limit int64, followLink bool) ([]Object, bool, string, error) {
	ds.metaMu.RLock()
	defer ds.metaMu.RUnlock()

	var obs []Object
	for k, v := range ds.objectIndex {
		if !strings.HasPrefix(k, prefix) {
			continue
		}
		if k <= startAfter {
			continue
		}
		obs = append(obs, &objWrap{key: v.key, size: v.size})
		if limit > 0 && int64(len(obs)) >= limit {
			// truncated
			return obs, true, v.key, nil
		}
	}
	return obs, false, "", nil
}

// ListAll returns a channel that will produce all objects under a prefix.
func (ds *daxStore) ListAll(prefix, marker string, followLink bool) (<-chan Object, error) {
	ch := make(chan Object, 128)

	go func() {
		defer close(ch)
		logger.Debugf("ListAll(): Closing ListAll channel")
		ds.metaMu.RLock()
		defer ds.metaMu.RUnlock()
		for k, v := range ds.objectIndex {
			if !strings.HasPrefix(k, prefix) || k < marker {
				continue
			}
			logger.Debugf("ListAll(): Sending object to channel: key=%s, size=%d", v.key, v.size)
			ch <- &objWrap{key: v.key, size: v.size}
		}
	}()

	return ch, nil
}

// Close cleans up all resources, including unmapping the DAX device.
func (ds *daxStore) Close() error {
	// Before unmapping, ensure we persist the free list
	if err := ds.persistFreeList(); err != nil {
		// Log the error, but attempt to close anyway
		logger.Debugf("Close(): persistFreeList error during close: %v", err)
	}

	// Unmap and close the device
	if ds.data != nil {
		if err := unix.Munmap(ds.data); err != nil {
			return fmt.Errorf("failed to munmap dax device: %w", err)
		}
		ds.data = nil
		logger.Debugf("Successfully unmapped dax device '%s'", ds.devPath)
	}

	// Close the file descriptor
	if ds.fd != 0 {
		if err := unix.Close(ds.fd); err != nil {
			return fmt.Errorf("failed to close dax device: %w", err)
		}
		ds.fd = 0
		logger.Debugf("Successfully closed dax device file descriptor")
	}
	return nil
}

// StatFS provides filesystem statistics to the OS
func (ds *daxStore) StatFS(ctx context.Context, ino Ino, totalspace, availspace, iused, iavail *uint64) syscall.Errno {
	ds.metaMu.RLock()
	defer ds.metaMu.RUnlock()

	// TotalSize: total space allocated minus reserved header space
	actualTotalSize := ds.header.TotalSize - ds.header.FreeListOff
	*totalspace = uint64(actualTotalSize)

	// Calculate used space by iterating over all objects
	var usedSpace int64 = 0
	var usedInodes uint64 = 0
	for _, obj := range ds.objectIndex {
		usedSpace += obj.size
		usedInodes += 1 // Assuming one inode per object
	}

	// Available space: TotalSize - UsedSpace
	*availspace = uint64(actualTotalSize - usedSpace)

	// iused: Number of used inodes
	*iused = usedInodes

	// iavail: Number of available inodes (assuming a maximum inode limit)
	const maxInodes uint64 = 1000000 // Example maximum; adjust as needed
	if usedInodes >= maxInodes {
		*iavail = 0
	} else {
		*iavail = maxInodes - usedInodes
	}

	return 0 // Success
}

// -------------------------------------
//  Minimal Object Implementation
// -------------------------------------

// objWrap is a simple wrapper that implements the Object interface (from interface.go).
type objWrap struct {
	key  string
	size int64
}

// Implement the Object interface methods
func (o *objWrap) Key() string        { return o.key }       // object key
func (o *objWrap) Size() int64        { return o.size }      // object size in bytes
func (o *objWrap) ModTime() time.Time { return time.Time{} } // modification time
func (o *objWrap) IsDir() bool        { return false }       // is directory
func (o *objWrap) ETag() string       { return "" }          // ETag
func (o *objWrap) IsSymlink() bool    { return false }       // Symbolic links are not implemented/supported
func (o *objWrap) Mtime() time.Time   { return time.Time{} } // Modification Time
func (o *objWrap) ContentType() string { // content type
	return "application/octet-stream"
}
func (o *objWrap) StorageClass() string { // storage class
	return "STANDARD"
}
func (o *objWrap) Meta() map[string]string { // metadata
	return nil
}

// Register the DAX storage driver
// This is called from the init() function in the package.
func init() {
	Register("dax", newDaxStore)
}
