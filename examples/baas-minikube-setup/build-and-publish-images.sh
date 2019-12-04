#!/bin/bash

echo "Run this command from the baker root"

sbt baas-minikube-state/docker:publish
sbt baas-minikube-interactions/docker:publish
sbt baas-minikube-event-listener/docker:publish
sbt baas-client-example/docker:publish
