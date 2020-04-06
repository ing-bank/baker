#!/bin/bash

# bump this manually whenever breaking change occurs
SEM_VERSION=3.0

DATE=$(date +"%Y%m%d_%H%M%S")
COMMIT=$( git log --pretty=format:'%h' -n 1)
VERSION="${SEM_VERSION}-${DATE}-${COMMIT}"

echo "version in ThisBuild := \"${VERSION}\"" > ./version.sbt
