#!/usr/bin/env bash

###########################################################################
#Script Name	: createMinikubeNamespace.sh
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

minikube --vm-driver virtualbox --memory 8192 --cpus 4 start --insecure-registry=registry-all.docker.ing.net

hostIp=$(minikube ssh "route -n | grep ^0.0.0.0 | awk '{ print \$2 }'")

#Removes last \r symbol
hostIp=${hostIp%?}

dockerVars="--insecure-registry=registry-all.docker.ing.net --docker-env http_proxy=${hostIp}:3128 --docker-env https_proxy=${hostIp}:3128"

minikube stop

minikube --vm-driver virtualbox --memory 8192 --cpus 4 start --insecure-registry=registry-all.docker.ing.net ${dockerVars}

kubectl api-resources