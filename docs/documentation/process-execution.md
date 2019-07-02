# Process Execution

## Recap

On the [runtime](baker-runtime.md) page we discussed how you could initialize Baker and add your [recipe](dictionary.md#recipe) to it.

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
val recipeInstanceId = "a-unique-process-id"

// Tell Baker that we want to create a new process for a certain recipe.
baker.bake(recipe.recipeId, recipeInstanceId)
```

```java tab="Java"
// Assuming you have a compiled recipe
CompiledRecipe recipe = null; //

// A unique identifier ment to distinguish this process from other process instances
String recipeInstanceId = "a-unique-process-id";

// Tell Baker that we want to create a new process for a certain recipe.
baker.bake(recipe.recipeId(), recipeInstanceId);
```

## Providing a sensory event

In our [webshop example](../index.md#visual-representation) the first events that can happen are `OrderPlaced`, `PaymentMade` and `CustomerInfoReceived`.

These are so called [sensory events](dictionary.md#sensory-event) since they are not the result of an interaction but must be provided by the user of Baker.

```scala tab="Scala"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
val customerInfo = CustomerInfo("John", "Elm. Street", "johndoe@example.com")
val order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` sensory Events.
baker.processEvent(recipeInstanceId, CustomerInfoRecived(customerInfo))
baker.processEvent(recipeInstanceId, OrderPlaced(order))
```

```java tab="Java"
// The CustomerInfoReceived and OrderPlaced events require some data (Ingredients)
CustomerInfo customerInfo = new CustomerInfo("John", "Elm. Street", "johndoe@example.com");
String order = "123";

// Lets produce the `OrderPlaced` and `CustomerInfoReceived` sensory Events.
baker.processEvent(recipeInstanceId, new CustomerInfoReceived(customerInfo));
baker.processEvent(recipeInstanceId, new OrderPlaced(order));
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

val statusA: SensoryEventStatus = baker.processEvent(recipeInstanceId, new OrderPlaced(order), orderId)
val statusB: SensoryEventStatus = baker.processEvent(recipeInstanceId, new OrderPlaced(order), orderId)

// statusA == Received
// statusB == AlreadyReceived

```

``` java tab="Java"
String orderId = "a unique order id";

SensoryEventStatus statusA = baker.processEvent(recipeInstanceId, new OrderPlaced(order), orderId);
SensoryEventStatus statusB = baker.processEvent(recipeInstanceId, new OrderPlaced(order), orderId);

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

## Incident resolving

It is possible that during execution a process instance becomes *blocked*.

This can happen either because it is [directly blocked](recipe-dsl.md#block-interaction) by a exception or that the retry strategy was exhuasted.

At this point it is possible to resolve the blocked interaction in 2 ways.

### 1. Force retry

For example, the retry strategy for *"SendInvoice"* was exhausted after a few hours or retrying.

However, we checked and know the *"invoice"* service is up again and want to continue to process for our customer.

``` scala tab="Scala"
baker.retryInteraction(recipeInstanceId, "SendInvoice")
```

``` java tab="Java"
baker.retryInteraction(recipeInstanceId, "SendInvoice");
```

### 2. Specify the interaction output

For example, the *"ShipGoods"* backend service is not idempotent and failed with an exception. It is not retried but *blocked*.

However, we checked and know the goods were actually shipped and want to continue the process for our customer.

``` scala tab="Scala"
baker.resolveInteraction(recipeInstanceId, "ShipGoods", GoodsShipped("some goods"))
```

``` java tab="Java"
baker.resolveInteraction(recipeInstanceId, "ShipGoods", new GoodsShipped("some goods"));
```

Note that the event provided *SHOULD NOT* include any [event or ingredient renames](recipe-dsl.md#event-renames) specified for the interaction.


## State inquiry

During runtime it is often useful to *inquire* on the state of a process instance.

## Visualize process instance state


We can use the visualizer to see what Baker has done with the given events.

```scala tab="Scala"
val dotRepresentation: String = baker.getVisualState(recipeInstanceId)
```

```java tab="Java"
String dotRepresentation = baker.getVisualState(recipeInstanceId);
```

!!! hint "Did you know?!"
    You can ask baker for a visual representation of a certain process.
    That way you can see which Events were provided and which Interaction were run.
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
val events: Seq[RuntimeEvent] = baker.getEvents(recipeInstanceId)
if (events.exists(_.name == "InvoiceWasSend"))
    // Yes the invoice was send!
```

```java tab="Java"
// Get all events that have happend for this process instance
EventList events = baker.getEvents(recipeInstanceId);
if (events.hasEventOccurred(InvoiceWasSend.class))
    // Yes the invoice was send!
```

### Ingredients

Sometimes it is useful to know what the ingredient values are accumulated for a process instance.

For example, you might want to know the value of the `trackingId`.

```scala tab="Scala"
// Get all ingredients that are accumulated for a process instance
val ingredients: Map[String, Value] = baker.getIngredients(recipeInstanceId)

val trackingId: String = ingredients("trackingId").as[String]
```

```java tab="Java"
// Get all ingredients that are accumulated for a process instance
Map<String, Value> ingredients = baker.getIngredients(recipeInstanceId);

String trackingId = ingredients.get("trackingId").as(String.class);
```

