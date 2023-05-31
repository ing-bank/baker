# Tutorial

This guide walks you through the process of creating a Baker orchestration workflow one step at a time. Completing
this tutorial takes around 20 minutes. 

!!! note
    To follow this tutorial you will need a Java, Kotlin, or Scala project that includes the dependencies mentioned in
    the [quickstart guide](../quickstart-guide).

!!! info
    This tutorial assumes you have a basic understanding of `ingredients`, `events`, `interactions`, and `recipes`. If
    not, please read the [concepts section](../concepts) before starting the tutorial.

## Setting the stage

Imagine you are working as a software engineer for a modern e-commerce company. They are building a web-shop made up of 
different microservices. You are responsible for orchestrating the order-flow. The requirements read:

!!! quote ""
    Once a customer places an order, we need to verify if the
    products are in stock. Stock levels are available via the `StockService`. If there is enough stock, ship the order
    by calling the `ShippingService`. If there is insufficient stock, cancel the order by calling the 
    `CancellationService`.

## Define the sensory event

A recipe is always triggered by a `sensory event`. In this example, our sensory event is the customer placing an order.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/events/OrderPlaced.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/events/OrderPlaced.kt"
    ```

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/events/OrderPlaced.scala"
    ```

The `OrderPlaced` event carries four ingredients. The `address` ingredient is of type `Address`, which is just a simple
data class.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/ingredients/Address.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/ingredients/Address.kt"
    ```

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/ingredients/Address.scala"
    ```

## Define the interactions
Next, it's time to model our interactions. We need to create a total of three interactions. One to validate if the products
are in stock, one to ship the order, and one to cancel the order. 

In this step we will just declare our interaction blueprints as interfaces. That's all we need to be able to declare 
a recipe. The implementation for these interactions will follow at a later stage.

### Check stock

Our stock validation interaction requires two ingredients as input. The `orderId` and a list of `productIds`. The
interaction won't execute unless these ingredients are available in the process. The interaction will either emit
a `Success` event, if all products are in stock. Or an `OrderHasUnavailableItems` event otherwise. 
The `OrderHasUnavailableItems` event carries a list of `unavailableProductIds` as ingredient.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/CheckStock.java"
    ```
    
    !!! info
        The `@FiresEvent` annotation is used to define the possible outcome events.

    !!! info
        The `@RequiresIngredient` annotation is used to define the ingredient names that this interaction needs for its
        execution.

    !!! warning
        The Java implementation makes use of Bakers reflection API. For this to work, the method in the
        interaction must be named `apply`. Other names won't work.

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/CheckStock.kt"
    ```

    !!! info
        Kotlin's reflection API is more powerful than Java's. There is no need for any annotations when you model the
        possible outcome events as a `sealed` hierarchy.

    !!! warning
        The Kotlin implementation makes use of Bakers reflection API. For this to work, the method in the
        interaction must be named `apply`. Other names won't work.

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/interactions/CheckStock.scala"
    ```

### Ship Order

To ship an order we'll need the `orderId` and an `address`. For the sake of simplicity, this interaction will always 
result in a `Success` event.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/ShipOrder.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/ShipOrder.kt"
    ```

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/interactions/ShipOrder.scala"
    ```

### Cancel order

To cancel the order we'll need the `orderId` and a list of `unavailableProductIds`. Of course, `unavailableProductIds`
will only be available if the stock validation failed.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/CancelOrder.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/CancelOrder.kt"
    ```

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/interactions/CancelOrder.scala"
    ```

## Define the recipe

At this point we can compose our sensory event and three interactions into a recipe. The `OrderPlaced` event is declared
as a sensory event. `OrderPlaced` carries all the ingredients required by the `CheckStock` interaction, so once the
sensory event fires the `CheckStock` interaction will execute.

`CheckStock` will output either a `Success` or `OrderHasUnavailableItems` event. `ShipOrder` will only execute if the
process contains an event of `CheckStock.Success` and `CancelOrder` will only execute if the process contains an event
of `CheckStock.OrderHasUnavailableItems`.

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/recipes/WebShopRecipe.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/recipes/WebShopRecipe.kt"
    ```

=== "Scala"
    ```scala
    --8<-- "docs-code-snippets/src/main/scala/examples/scala/recipes/WebShopRecipe.scala"
    ```

## Implement the interactions

Before we can run our recipe, we need to create InteractionInstances that the Baker runtime will use to execute the 
interactions. In other words, we need to provide implementations for the interactions.

Since this is a tutorial, we'll just create some dummy implementations. In a real solution, this is the part where you
would implement your API calls to the other systems.

!!! tip
    These examples use a `Impl` suffix for our implementations. In your real solution you might want to use a more 
    meaningful name. 

### Check stock implementation

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/CheckStockImpl.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/CheckStockImpl.kt"
    ```

=== "Scala"
    ```scala
    TODO add Scala example!
    ```

### Ship order implementation

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/ShipOrderImpl.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/ShipOrderImpl.kt"
    ```

=== "Scala"
    ```scala
    TODO add Scala example!
    ```

### Cancel order implementation

=== "Java"
    ```java
    --8<-- "docs-code-snippets/src/main/java/examples/java/interactions/CancelOrderImpl.java"
    ```

=== "Kotlin"
    ```kotlin
    --8<-- "docs-code-snippets/src/main/kotlin/examples/kotlin/interactions/CancelOrderImpl.kt"
    ```

=== "Scala"
    ```scala
    TODO add Scala example!
    ```

## Execute the recipe

Add some stuff about recipe execution here.

!!! note
    Kotlin function is suspending because...

## Wrap-up
