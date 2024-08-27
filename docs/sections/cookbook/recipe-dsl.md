# Recipe DSL

!!! Warning
    The examples in this section are set up to demonstrate specific features of the recipe DSL. The snippets are not
    complete recipes. For example, some snippets only specify sensory events without any interactions,
    and vice versa.

## Sensory events

### Firing limit

Sensory events can be declared with or without firing limit. The firing limit determines how many times the event is
allowed to be fired into the process. If you don't want to impose any limits, you have to explicitly declare the event
as such. If left unspecified, the firing limit defaults to 1.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithSensoryEvents.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithSensoryEvents.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithSensoryEvents.scala"
    ```
    
    !!! Note
        For Scala events the `maxFiringLimit` is set in the `Event` definition. An example event definition can be
        found in [this section](../../tutorial#define-the-sensory-event) of the tutorial.

### Event receive period
The period during which the process accepts sensory events. This is an optional parameter, defaults to accepting 
sensory events forever.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithEventReceivePeriod.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithEventReceivePeriod.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithEventReceivePeriod.scala"
    ```

## Interactions

### Custom name
By default, the name of the interaction matches the name of the interaction class. Optionally, you can specify your
own name.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/InteractionWithCustomName.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/InteractionWithCustomName.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/InteractionWithCustomName.scala"
    ```


### Maximum interaction count
By default, an interaction can be invoked an unlimited amount of times. Optionally, you can specify a limit.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithMaxInteractionCount.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithMaxInteractionCount.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithMaxInteractionCount.scala"
    ```

### Predefined ingredients
It's possible to register static ingredients to the interaction via predefined ingredients.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithPreDefinedIngredients.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithPreDefinedIngredients.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithPreDefinedIngredients.scala"
    ```

### Required events
Sometimes an interaction should only execute after a certain event has happened. To achieve this you can specify
`requiredEvents` or `requiredOneOfEvents`. 

All required events have to be available for the interaction to be executed. It works as a logical AND. In contrast, 
required one of events works as a logical OR. At least one of those events should be available before the interaction
is executed. 

In this example, the `ShipOrder` interaction will only execute if the `FraudCheckCompleted` and one of (or both) the 
`PaymentReceived` or `UsedCouponCode` events are available.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithRequiredEvents.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithRequiredEvents.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithRequiredEvents.scala"
    ```

### Transform output events

It's possible to change the name of an output event. Optionally, you can also change names of 
ingredients.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithEventTransformation.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithEventTransformation.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithEventTransformation.scala"
    ```

### Override input ingredients

It's possible to change the names the input ingredients.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithIngredientNameOverrides.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithIngredientNameOverrides.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithIngredientNameOverrides.scala"
    ```

### Failure strategy
It's possible to define a failure strategy on interaction level. This failure strategy will only be used for this
specific interaction. Interaction specific failure strategies take precedence over the default failure strategy. 
For all available failure strategies, see the [error handling](/sections/cookbook/error-handling) section.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithFailureStrategy.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithFailureStrategy.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithFailureStrategy.scala"
    ```

## Recipe

### Retention period
The period during which the process keeps running, the recipe will be deleted AFTER the retention period has passed (measured from the creation time of the Recipe instance. This is an optional parameter, defaults to keep the process forever.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithRetentionPeriod.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithRetentionPeriod.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithRetentionPeriod.scala"
    ```

### Checkpoint events
Checkpoints are used to fire an event with a given name whenever certain preconditions are met. The preconditions 
are specified via `requiredEvents` or `requiredOneOfEvents`.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithCheckpointEvent.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithCheckpointEvent.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithCheckpointEvent.scala"
    ```

### Default failure strategy
The default failure strategy allows you to set a failure strategy for interactions that don't specify 
one explicitly. For all available failure strategies, see the [error handling](/sections/cookbook/error-handling) section.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/RecipeWithDefaultFailureStrategy.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/RecipeWithDefaultFailureStrategy.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/RecipeWithDefaultFailureStrategy.scala"
    ```
