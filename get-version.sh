#!/bin/bash
DIR=$(dirname $0)
cat $DIR/version.sbt | sed 's/version in ThisBuild := \"\([0-9]*\)\.\([0-9]*\)\.\([0-9]*\).*/\1.\2.\3/'
