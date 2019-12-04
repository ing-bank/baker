#!/bin/bash

echo "Run this command from the baker root"

sbt baas-minikube-state/docker:publish
sbt baas-minikube-interactions/docker:publish
sbt baas-minikube-event-listener/docker:publish
sbt baas-client-example/docker:publish

#docker push apollo.docker.ing.net/baas-minikube-state:3.0.2
#docker push apollo.docker.ing.net/baas-minikube-interactions:3.0.2
#docker push apollo.docker.ing.net/baas-minikube-event-listener:3.0.2
#docker push apollo.docker.ing.net/baas-client-example:3.0.2

