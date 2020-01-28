#!/bin/bash

echo "Run this command from the baker root"

sbt baas-minikube-state/docker:publish
sbt make-payment/docker:publish
sbt reserve-items/docker:publish
sbt ship-items/docker:publish
sbt baas-minikube-event-listener/docker:publish
sbt baas-client-example/docker:publish
