#!/bin/bash

# bump this manually whenever change occurs
SEM_VERSION=3.0.2

DATE=$(date +"%Y%m%d_%H%M%S")
COMMIT=$( git log --pretty=format:'%h' -n 1)

VERSION="${SEM_VERSION}-${DATE}-${COMMIT}"

echo "version in ThisBuild := \"${VERSION}\"" > ./version.sbt

cat ./version.sbt
