#!/usr/bin/env bash
IMAGE=wangpengmit/timl
docker build -t $IMAGE .
docker run -it -p 8080:8888 $IMAGE
