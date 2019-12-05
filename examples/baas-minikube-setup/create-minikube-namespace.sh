#!/usr/bin/env bash

###########################################################################
#Script Name	: create-minikube-example.sh
#Description	: Creates and runs new minikube instance using preproxy
#Args         : Not supported
#Bash Version : GNU bash, version 3.x.XX
###########################################################################

set -o errexit
set -eo pipefail
set -o nounset
#set -o xtrace

RED='\033[0;31m'
NC='\033[0m' # No Color

echo -e "Creating minikube cluster locally ${RED}(takes up to 10 minutes)${NC}"
minikube delete || echo "Ignoring delete for non existed minikube cluster"

minikube --vm-driver virtualbox --memory 8192 --cpus 4 start

kubectl api-resources