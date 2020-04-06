#!/bin/bash

# bump this manually whenever change occurs
SEM_VERSION=3.0.2

BRANCH=$(git branch | sed -n -e 's/^\* \(.*\)/\1/p' | sed -e 's#/#_#g')
DATE=$(date +"%Y%m%d_%H%M%S")
COMMIT=$( git log --pretty=format:'%h' -n 1)

if [ "$BRANCH" = "master" ]; then BRANCH=""; else BRANCH="-${BRANCH}"; fi

VERSION="${SEM_VERSION}${BRANCH}-${DATE}-${COMMIT}"

echo "version in ThisBuild := \"${VERSION}\"" > version.sbt
