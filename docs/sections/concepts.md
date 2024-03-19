# Concepts

In Baker, you declare orchestration logic as a `Recipe`. A recipe consists of three main building blocks:
`Ingredients`, `Interactions`, and `Events`. 

## Ingredient

An ingredient is a combination of a `name` and `type`. Similar to how a variable declaration in your codebase is a combination
of a name and type. For example, you can have an ingredient with the name `iban` and type `string`. Types are expressed
via the [Baker type system](../reference/baker-types-and-values/).

Ingredients are pure pieces of data. They are immutable, meaning they do not change once they enter the process or
workflow. There is no support for hierarchy. Expressing a relationship like `Animal -> Dog -> Labrador` is not possible.

Ingredients serve as input for interactions and are carried through the process via
events.

## Event

Events represent something that has happened in your process. Most of the time, events are outputs of interactions.
We refer to outputs of interactions as `internal events`. Sometimes events come from outside the process. we refer to 
events from outside the process as `sensory events`. Sensory events start/trigger the process. 

!!! note
    Under the hood `internal events` and `sensory events` are identical. The naming distinction exists for practical 
    reasons only.

An event has a `name` and (optionally) provides ingredients. In the end, events and ingredients are just data structures
that describe your process data. A good example would be an `OrderPlaced` event which carries two ingredients:
the `orderId` and a `list of products`.

## Interaction

Interactions resemble functions. They require input (ingredients) and provide output (events). An
interaction can do many things. For example, fetch data from another service, do some complex calculation, 
send a message to an event broker, etc.

## Recipe

A recipe is the blueprint of your business process. You define this process by combining ingredients, events, and
interactions. Baker provides a recipe DSL, allowing you to define your recipe in Java, Kotlin, or Scala. The example
below displays a (naive) recipe implementation to ship orders from a web-shop. 

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/SimpleRecipe.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/SimpleRecipe.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/SimpleRecipe.scala"
    ```
