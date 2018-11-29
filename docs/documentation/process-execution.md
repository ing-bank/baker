# Process Execution

## Recap

On the [runtime](runtime.md) page we discussed how you could could add your [Recipe](dictionary.md#recipe) to Baker.

Lets summarize what we have done so far.

```java
// To execute a recipe you will need Baker again
// This should be the same Baker instance as you used to register your Recipe
JBaker baker = ...;

// The recipe was given to us when we Bakes our Recipe
String recipeId = "...";
```

## Create a process instance

Given a valid Baker a [Recipe id](dictionary.md#recipe-id) we can now execute a Recipe.

Or in other words we can create a [Process instance](dictionary.md#process-instance).


```java
// A unique processId ment to distinct this process from other process instances
// We use a random UUID but you could use whatever you like.
String processId = UUID.randomUUID().toString();

// Tell Baker that we want to register a new process for a certain recipe.
baker.bake(recipeId, processId);
```

## Process an event

In our webshop example the first events that can happen are `OrderPlaced` `PaymentMade` and `CustomerInfoReceived`.

These are so called [Sensory events](dictionary.md#sensory-event) as can be [seen is a starting point for our webshop example](../index.md#visual-representation).

```java
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

```java
String dotRepresentation baker.getVisualState(processId);
```

!!! hint "Did you know?!"
    You can ask baker for a visual representation of a certain process.
    That way you can see which Events where provided and which Interaction are ran.
    [See the visualization page how to create a visual graph.](recipe-visualization.md)

![](/images/webshop-state-1.svg)

