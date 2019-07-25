## Introduction

Baker is a library that reduces the effort to orchestrate (micro)service-based process flows.

Developers declare the orchestration logic in a *Recipe* (process blueprint).

A *Recipe* is made out of:

- *Interactions* (functions)
- *Ingredients* (data)
- *Events*

More about these concepts [here](../sections/reference).

## Overview

Baker allows you to:

- *Declaritavely* design your processes using a [recipe DSL](recipe-dsl.md).
- [Visualize](recipe-visualization.md) your recipe allowing product owners, architects and developers to talk the same language.
- Manage your recipes using the [baker runtime](baker-runtime.md).
- [Create process instances](process-execution.md#create-a-process-instance) of your recipes.
- [Fire sensory events](process-execution.md#providing-a-sensory-event).
- [Inquire the state](process-execution.md#state-inquiry) of your process instances.

## Visual representation

Below an example of a simple web shop recipe:

![](../images/webshop.svg)
