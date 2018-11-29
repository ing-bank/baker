## Introduction

Baker is a library that reduces the effort to orchestrate (micro)service-based process flows.

Developers declare the orchestration logic in a *Recipe* (process blueprint).

A *Recipe* is made out of:

- *Interactions* (functions)
- *Ingredients* (data)
- *Events*

More about these concepts [here](documentation/concepts).

## Overview

Baker allows you to:

- *Declaritavely* design your processes using a [recipe DSL](recipe-dsl.md).
- Manage your recipes using the [baker runtime](runtime.md).
- [Create](process-execution.md#create-a-process-instance) process instances of your recipes.
- [Fire](process-execution.md#) sensory events.
- Inquire the state of your process instances.

## Visual representation

A visual representation of the recipe allows product owners, architects and developers to talk the same language:

![](images/webshop.svg)
