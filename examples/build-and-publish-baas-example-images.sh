#!/bin/bash

echo "Run this command from the baker root"

sbt baas-node-state/docker:publishLocal
sbt baas-client-example/docker:publishLocal
sbt baas-interaction-example-make-payment/docker:publishLocal
sbt baas-interaction-example-reserve-items/docker:publishLocal
sbt baas-interaction-example-ship-items/docker:publishLocal
sbt baas-event-listener-example/docker:publishLocal
