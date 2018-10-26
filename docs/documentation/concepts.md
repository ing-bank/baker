# Concepts

Baker introduces *interactions*, *ingredients*, and *events* as a model of abstracting.

With these three components we can create recipes (process blue prints)

## Ingredient

Ingredients are *pure data*.

This data is **immutable**, can not be changed after entering the process.

There is **no hiërarchy** in this data. (`Animal -> Dog -> Labrador` is not possible to express)

Examples:

- an IBAN
- an address
- a track and trace code
- a product number
- a list of phone numbers

An ingredient is defined by a *name* and *type*.

The *name* points to the intended meaning of the data. ("customerData", "orderNumber", ...)

The *type* sets limits on the form of data that is accepted. (a number, a list of strings, ...)

This type is expressed by the [baker type system](type_system).

## Interaction

An interaction is analagous to a function.

It requires *input* ([ingredients](#ingredient)) and provides *output* ([events](#event)).

Within this contract it may do anything. For example:

- query an external system
- put a message on a bus
- generate a document or image
- extract or compose ingredients into others

When finished, an interaction provides an event as its output.

### Failure

We distinquish 2 types of failures.

1. A *technical* failure is one that could be retried and succeed. For example:
    * Time outs because of unreliable network, packet loss
    * External system is temporarily down or unresponsive
    * External system returned a malformed/unexpected response

    These failures are unexpected and are are modeled by throwing an exception from the interaction.

2. A *functional* failure is one that cannot be retried. For example:
    * The customer is too young for the request.
    * Not enough credit to perform the transfer.

    These failures are expected possible outcomes of the interaction.

    They are modelled by returning an event from the interaction.

### Failure mitigation (Failure strategies)

In case of technical failures, baker offers 2 mitigation strategies:

1. Retry with incremental backoff

    This retries the interaction after some time. Configurable options:

    `initialTimeout=100 milliseconds`, `backoffFactor=2`, `maximumInterval=10 minutes`, `period=24 hours`

2. Continue with an event.

    This is analagous to a try/catch in java code. The exception is logged but the process continues with a specified event.

When no failure strategy is defined for an interaction by default

## Event

Events indicate something of interest happened for our process.

An event has a *name* and can (optionally) provide ingredients.

We distinquish 2 types of events.

1. Sensory events (external)

    These events are provided from outside of the process

2. Interaction output (internal)

    These events are provided as a result of an interaction being executed.