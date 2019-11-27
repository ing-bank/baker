#!/bin/bash

set -eo pipefail
set -o nounset

# clean up first
namespace_name=default

function log () {
  echo -e "\n $1 \n"
}

log "Delete current deployments"
set +e
kubectl delete -f akka-cluster.yml | echo "Ignoring delete resources declared on akka-cluster.yml"
set -e

log "Check status of Minikube & start if stopped"

mini_running=$(minikube status | grep 'host:' | awk '{print $2}')

echo $mini_running

if [[ $mini_running == "Stopped" ]]; then
  sh ./createMinikubeNamespace.sh
  echo "Started minikube"
fi

log "Set to minikube env"

eval $(minikube docker-env)
kubectl config use-context minikube

log "Build new image"
# make sure minikube can access registry run : minikube delete  && minikube start --insecure-registry=registry-all.docker.ing.net

# Assuming current working directory is: ../baker/examples/baas-minikube-setup
cd ../..
sbt baas-minikube-state/docker:publishLocal
sbt baas-minikube-interactions/docker:publishLocal
sbt baas-minikube-event-listener/docker:publishLocal

cd examples/baas-minikube-setup

kubectl apply -f akka-cluster.yml
kubectl apply -f service.yml