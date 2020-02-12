#!/bin/bash

echo "Run this command from the baker root"

sbt \
baas-node-state/docker:publishLocal \
baas-client-example/docker:publishLocal \
baas-dashboard-server/docker:publishLocal \
baas-interaction-example-make-payment/docker:publishLocal \
baas-interaction-example-reserve-items/docker:publishLocal \
baas-interaction-example-ship-items/docker:publishLocal \
baas-event-listener-example/docker:publishLocal \
baas-baker-event-listener-example/docker:publishLocal
