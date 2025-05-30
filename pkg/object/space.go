//go:build !nos3
// +build !nos3

/*
 * JuiceFS, Copyright 2018 Juicedata, Inc.
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

package object

import (
	"fmt"
	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/credentials"
	"github.com/aws/aws-sdk-go-v2/service/s3"
	"net/url"
	"strings"
)

type space struct {
	s3client
}

func (s *space) String() string {
	return fmt.Sprintf("space://%s/", s.s3client.bucket)
}

func (s *space) Limits() Limits {
	return s.s3client.Limits()
}

func (s *space) SetStorageClass(sc string) error {
	return notSupported
}

func newSpace(endpoint, accessKey, secretKey, token string) (ObjectStorage, error) {
	if !strings.Contains(endpoint, "://") {
		endpoint = fmt.Sprintf("https://%s", endpoint)
	}
	uri, _ := url.ParseRequestURI(endpoint)
	ssl := strings.ToLower(uri.Scheme) == "https"
	hostParts := strings.Split(uri.Host, ".")
	bucket := hostParts[0]
	region := hostParts[1]
	endpoint = uri.Scheme + "://" + uri.Host[len(bucket)+1:]

	awsCfg, err := config.LoadDefaultConfig(ctx,
		config.WithCredentialsProvider(credentials.NewStaticCredentialsProvider(accessKey, secretKey, token)))
	if err != nil {
		return nil, fmt.Errorf("failed to load config: %s", err)
	}
	client := s3.NewFromConfig(awsCfg, func(options *s3.Options) {
		options.Region = region
		options.BaseEndpoint = aws.String(endpoint)
		options.EndpointOptions.DisableHTTPS = !ssl
		options.UsePathStyle = false
		options.HTTPClient = httpClient
	})
	return &space{s3client{bucket: bucket, s3: client, region: region}}, nil
}

func init() {
	Register("space", newSpace)
}
