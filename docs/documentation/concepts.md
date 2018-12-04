# Concepts

Baker introduces *interactions*, *ingredients*, and *events* as a model of abstracting.

With these three components we can create recipes (process blue prints)

## Ingredient

Ingredients are *pure data*.

This data is **immutable**, can not be changed after entering the process.

There is **no hiërarchy** in this data. (`Animal -> Dog -> Labrador` is not possible to express)

Examples:

- an IBAN
- a track and trace code
- a list of phone numbers
- a customer information object with name, email, etc ...

An ingredient is defined by a *name* and *type*.

The *name* points to the intended meaning of the data. ("customerData", "orderNumber", ...)

The *type* sets limits on the form of data that is accepted. (a number, a list of strings, ...)

This type is expressed by the [baker type system](type-system.md).

## Interaction

An interaction is analagous to a function.

It requires *input* ([ingredients](#ingredient)) and provides *output* ([events](#event)).

Within this contract it may do anything. For example:

- query an external system
- put a message on a bus
- generate a document or image
- extract or compose ingredients into others

When finished, an interaction provides an event as its output.

### Interaction failure

An interaction may fail to fulfill its intended purpose.

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

### Failure mitigation

In case of technical failures, baker offers 2 mitigation strategies:

1. Retry with incremental backoff

    This retries the interaction with some configurable parameters:

    - `initialTimeout`: The initial delay for the first retry.
    - `backoffFactor`: The backoff factor.
    - `maximumInterval`: The maximum interval between retries.

2. Continue with an event.

    This is analagous to a try/catch in java code. The exception is logged but the process continues with a specified event.

When no failure strategy is defined for an interaction by default the interaction is *blocked*.

## Event

An event has a *name* and can (optionally) provide ingredients.

The purpose of events is therefor twofold.

1. It signifies something of interest happened for a [process instance](dictionary.md#process-instance).

    Example, *"the customer placed the order"*, *"terms and conditions where accepted"*

2. The event may provide ingredients required to continue the process.

    Example, *"OrderPlaced"* -> `<list of products>`

We distinquish 2 types of events.

1. Sensory events (*external*)

    These events are provided from outside of the process.

2. Interaction output (*internal*)

    These events are a result of an interaction being executed.

## **Recipe**

*Events*, *Interactions* and *Ingredients* can be composed into recipes.

Recipes are analagous to process blueprints.

Baker provides a [Recipe DSL](recipe-dsl.md) in which you can declaritively describe your recipe.

A small example:
``` java
new Recipe("webshop")
    .withSensoryEvents(
        OrderPlaced.class,
        CustomerInfoReceived.class
    .withInteractions(
        of(ValidateOrder.class),
        of(ManufactureGoods.class));
```

The main take away is that when declaring your recipe you do not have to think about order.

Everything is automatically linked by the *data* requirements of the interactions.