#!/bin/bash

# bump this manually whenever breaking change occurs
SEM_VERSION=$(cat version.sbt | sed 's/version in ThisBuild := \"\([0-9]*\)\.\([0-9]*\)\.\([0-9]*\).*/\1.\2.\3/')

DATE=$(date +"%Y%m%d_%H%M%S")
COMMIT=$( git log --pretty=format:'%h' -n 1)
VERSION="${SEM_VERSION}-${DATE}-${COMMIT}"

echo "version in ThisBuild := \"${VERSION}\"" > ./version.sbt
