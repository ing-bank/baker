#!/bin/bash

DIR=$(dirname $0)
# bump this manually whenever breaking change occurs
SEM_VERSION=$($DIR/get-version.sh)

DATE=$(date +"%y%m%d%H%M%S")
COMMIT=$( git log --pretty=format:'%h' -n 1)
VERSION="${SEM_VERSION}-${DATE}-${COMMIT}"

echo "version in ThisBuild := \"${VERSION}\"" > ./version.sbt
