# Process Execution

## Recap

On the [runtime](baker-runtime.md) page we discussed how you could could initialize Baker and add your [recipe](dictionary.md#recipe) to it.

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
JBaker baker = null; //

// The recipe id was given to us when we add our Recipe to Baker
String recipeId = "...";
```

## Create a process instance

Given a valid [recipe id](dictionary.md#recipe-id) we can now execute a Recipe.

Or in other words we can create a [process instance](dictionary.md#process-instance).

```scala tab="Scala"
// Assuming you have a compiled recipe
val recipe: CompiledRecipe = ???

// A unique identifier ment to distinguish this process from other process instances
val processId = "a-unique-process-id"

// Tell Baker that we want to create a new process for a certain recipe.
baker.bake(recipe.recipeId, processId)
```

```java tab="Java"
// Assuming you have a compiled recipe
CompiledRecipe recipe = null; //

// A unique identifier ment to distinguish this process from other process instances
String processId = "a-unique-process-id";

// Tell Baker that we want to create a new process for a certain recipe.
baker.bake(recipe.recipeId(), processId);
```

## Providing a sensory event

In our [webshop example](../index.md#visual-representation) the first events that can happen are `OrderPlaced`, `PaymentMade` and `CustomerInfoReceived`.

These are so called [sensory events](dictionary.md#sensory-event) since they are not the result of an interaction but must be provided by the user of Baker.

```scala tab="Scala"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
val customerInfo = CustomerInfo("John", "Elm. Street", "johndoe@example.com")
val order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` sensory Events.
baker.processEvent(processId, CustomerInfoRecived(customerInfo))
baker.processEvent(processId, OrderPlaced(order))
```

```java tab="Java"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
CustomerInfo customerInfo = new CustomerInfo("John", "Elm. Street", "johndoe@example.com");
String order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` sensory Events.
baker.processEvent(processId, new CustomerInfoReceived(customerInfo));
baker.processEvent(processId, new OrderPlaced(order));
```

When receiving events Baker will check which Interactions have all the required Ingredients and Events met.

It will execute those interactions.

Those interactions will raise more events.

For more information about the exact execution sementics see [here](execution-semantics.md).

### Correlation id

Optionally you may provide a `correlation id` with an event. The purpose of this identifier is idempotent event delivery.

When sending the same event correlation id multiple times, only the first will be processed.

This can be applied to the `OrderPlaced` event for example.

``` scala tab="Scala"
val orderId = "a unique order id"

val statusA: SensoryEventStatus = baker.processEvent(processId, new OrderPlaced(order), orderId)
val statusB: SensoryEventStatus = baker.processEvent(processId, new OrderPlaced(order), orderId)

// statusA == Received
// statusB == AlreadyReceived

```

``` java tab="Java"
String orderId = "a unique order id";

SensoryEventStatus statusA = baker.processEvent(processId, new OrderPlaced(order), orderId);
SensoryEventStatus statusB = baker.processEvent(processId, new OrderPlaced(order), orderId);

// statusA == Received
// statusB == AlreadyReceived

```

## Sensory event status

In response to recieving a sensory event baker returns a status code indicating how it processed it.

| Status | Description |
| --- | --- |
| `Received` | The event was received normally |
| `AlreadyReceived` | An event with the same correlation id was already received |
| `ProcessDeleted` | The process instance was deleted |
| `ReceivePeriodExpired` | The receive period for the process instance has passed |
| `FiringLimitMet` | The [firing limit](recipe-dsl.md#firing-limit) for the event was met |

## State inquiry

During runtime it is often useful to *inquire* on the state of a process instance.

## Visualize process instance state


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


### Events

We can ask Baker for a list of all the events for our process.

Using this list we can check if the `InvoiceWasSend` event was produced.

```scala tab="Scala"
// Get all events that have happend for this process instance
val events: Seq[RuntimeEvent] = baker.getEvents(processId)
if (events.exists(_.name == "InvoiceWasSend"))
    // Yes the invoice was send!
```

```java tab="Java"
// Get all events that have happend for this process instance
EventList events = baker.getEvents(processId);
if (events.hasEventOccured(InvoiceWasSend.class))
    // Yes the invoice was send!
```

### Ingredients

Sometimes it is useful to know what the ingredient values are accumulated for a process instance.

For example, you might want to know the value of the `trackingId`.

```scala tab="Scala"
// Get all ingredients that are accumulated for a process instance
val ingredients: Map[String, Value] = baker.getIngredients(processId)

val trackingId: String = ingredients("trackingId").as[String]
```

```java tab="Java"
// Get all ingredients that are accumulated for a process instance
Map<String, Value> ingredients = baker.getIngredients(processId);

String trackingId = ingredients.get("trackingId").as(String.class);
```

