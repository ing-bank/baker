# Process Execution

## Recap

On the [runtime](runtime.md) page we discussed how you could could add your [Recipe](dictionary.md#recipe) to Baker.

Lets summarize what we have done so far.

```scala tab="Scala"
// To execute a recipe you will need a Baker instance
// This should be the same instance as you used to register your Recipe
val baker: Baker = ???

// The recipe id was given to us when we add our Recipe to Baker
val recipeId: String = ???
```

```java tab="Java"
// To execute a recipe you will need a Baker instance
// This should be the same instance as you used to register your Recipe
JBaker baker = ...;

// The recipe id was given to us when we add our Recipe to Baker
String recipeId = "...";
```

## Create a process instance

Given a valid Baker a [Recipe id](dictionary.md#recipe-id) we can now execute a Recipe.

Or in other words we can create a [Process instance](dictionary.md#process-instance).

```scala tab="Scala"
// A unique processId ment to distinct this process from other process instances
val processId = "a-unique-process-id"

// Tell Baker that we want to register a new process for a certain recipe.
baker.bake(recipeId, processId)
```

```java tab="Java"
// A unique processId ment to distinct this process from other process instances
// We use a random UUID but you could use whatever you like.
String processId = "a-unique-process-id"

// Tell Baker that we want to register a new process for a certain recipe.
baker.bake(recipeId, processId);
```

## Process an event

In our webshop example the first events that can happen are `OrderPlaced` `PaymentMade` and `CustomerInfoReceived`.

These are so called [Sensory events](dictionary.md#sensory-event) as can be [seen is a starting point for our webshop example](../index.md#visual-representation).

```scala tab="Scala"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
val customerInfo = CustomerInfo("John", "Elm. Street", "johndoe@example.com")
val order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` Sensory Events.
baker.processEvent(processId, CustomerInfoRecived(customerInfo))
baker.processEvent(processId, OrderPlaced(order))
```

```java tab="Java"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
CustomerInfo customerInfo = new CustomerInfo("John", "Elm. Street", "johndoe@example.com");
String order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` Sensory Events.
baker.processEvent(processId, new CustomerInfoRecived(customerInfo));
baker.processEvent(processId, new OrderPlaced(order));
```

## Visualize process state

When processing events Baker will check which Interactions have all the required Ingredients and Events in order to execute.

Baker will continue to do so until there are no Interactions left to execute.

We can use the visualizer to see what Baker has done with the given events.

```scala tab="Scala"
val dotRepresentation: String = baker.getVisualState(processId)
```

```java tab="Java"
String dotRepresentation = baker.getVisualState(processId);
```

!!! hint "Did you know?!"
    You can ask baker for a visual representation of a certain process.
    That way you can see which Events where provided and which Interaction are ran.
    [See the visualization page how to create a visual graph.](recipe-visualization.md)

![](/images/webshop-state-1.svg)

The image shows us that the `ValidateOrder` Interaction is colored green which means that the Interaction has been exucuted. Baker was able to exeucte the Interaction because all required Events and Ingredients where provided.
The `ValidateOrder` Interaction in turn produced the `Valid` event.

We can also see that the `ManufactureGoods` Interaction is still purple, meaning that it has not been executed. This is correct because `ManufactureGoods` requires an additional event called `PaymentMade`.

## Adding aditional Sensory events to the process

Lets provide the `PaymentMade` event and review the process status afterwards.

```scala tab="Scala"
// Provide the PaymentMade sensory event
baker.processEvent(processId, PaymentMade())

// Check the dot representation of the current state again
val dotRepresentation: String = baker.getVisualState(processId)
```

```java tab="Java"
// Provide the PaymentMade sensory event
baker.processEvent(processId, new PaymentMade());

// Check the dot representation of the current state again
String dotRepresentation = baker.getVisualState(processId);
```

Visualizing the new state will give us the following image.

![](/images/webshop-state-2.svg)


