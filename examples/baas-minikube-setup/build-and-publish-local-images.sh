#!/bin/bash

echo "Run this command from the baker root"

sbt baas-minikube-state/docker:publishLocal
sbt baas-minikube-interactions/docker:publishLocal
sbt baas-minikube-event-listener/docker:publishLocal
sbt baas-client-example/docker:publishLocal
