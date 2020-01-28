#!/bin/bash

echo "Run this command from the baker root"

sbt baas-minikube-state/docker:publishLocal
sbt make-payment/docker:publishLocal
sbt reserve-items/docker:publishLocal
sbt ship-items/docker:publishLocal
sbt baas-minikube-event-listener/docker:publishLocal
sbt baas-client-example/docker:publishLocal
