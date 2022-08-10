The `bakery` directory contains modules for setting up a bakery cluster.

Bakery is a way to host a baker service using akka-runtime and expose it using API endpoints. This allows you to separate
the running of an akka cluster and managing of the persistence from using baker for your business process.

A bakery team can provide baker clusters as a service (which requires specific knowledge about akka clusters).
A client team can focus on creating recipes based on actual business processes.

The `bakery-state` module is the entry point for bakery.
