/*
 * JuiceFS, Copyright 2020 Juicedata, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package fuse

import (
	"github.com/hanwen/go-fuse/v2/fuse"
)

func getCreateUmask(mask uint32, defMask uint16) uint16 {
	if defMask != 0xFFFF {
		return defMask
	}
	return uint16(mask)
}

func getUmask(mask uint32, defMask uint16, isDir bool) uint16 {
	if defMask != 0xFFFF {
		return defMask
	}
	return uint16(mask)
}

func setBlksize(out *fuse.Attr, size uint32) {
	out.Blksize = size
}
