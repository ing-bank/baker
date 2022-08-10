The `http` directory contains the modules for exposing or consuming baker using http(s). This allows for baker to be called
from other APIs (see the `bakery` directory) or even from non-jvm applications (for example javascript).

The `http` directory also contains the `baker-http-dashboard` project which uses the endpoints exposed by the `baker-http-server` library to allow you
to view added recipes, inspect and execute interactions manually, or inspect the status of process instances (executed recipes).
