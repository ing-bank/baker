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

It requires input (ingredients) and provides output (an event).

Within this contract it may do anything. For example:

- call an external system
- put a message on a bus
- generate a document or image
- extract or compose ingredients into others

When finished, an interaction provides an event as its output.

## Event

Events indicate something of interest happened for our process.

An event has a *name* and can (optionally) provide ingredients.

We distinquish 2 types of events.

1. Sensory events (external)

    These events are provided from outside of the process

2. Interaction output (internal)

    These events are provided as a result of an interaction being executed.