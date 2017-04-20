#!/usr/bin/env bash
docker build -t timl .
docker run -it -p 4000:8888 timl
