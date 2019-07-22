# The Akka Based Runtime

## Baker.akka(config, actorSystem, materializer)

Baker provider several constructors to build a runtime to run your Recipes on. The current implementations are o
[Akka](https://akka.io/) based, one in local mode, and another in cluster mode. 

_Note: We recommend reviewing also Akka configuration._

```scala tab="Scala"
import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.config.{Config, ConfigFactory}


val actorSystem: ActorSystem = ActorSystem("WebshopSystem")
val materializer: Materializer = ActorMaterializer()
val config: Config = ConfigFactory.load()

val baker: Baker = Baker.akka(config, actorSystem, materializer)
```

```java tab="Java"
import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.runtime.javadsl.Baker;
import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;


ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Materializer materializer = ActorMaterializer.create(actorSystem);
Config config = ConfigFactory.load();

Baker baker = Baker.akka(config, actorSystem, materializer);
```

This last code snippet will build a Baker runtime and load all configuration from your default `application.conf` located 
in the resources directory. You can see more about configuration on [this section](../development-life-cycle/configure.md).

Alternatively there is a constructor that will provide the default configuration for a local mode Baker, this 
is recommended for tests.

```scala tab="Scala"

val baker: Baker = Baker.akkaLocalDefault(actorSystem, materializer)

```

```java tab="Java"

Baker baker = Baker.akkaLocalDefault(actorSystem, materializer);

```

## InteractionInstance.from(object) (Reflection API)

As part of our efforts to ease the creation of `InteractionInstances` we created this function that uses the Scala and the
Java reflection capabilities to create an `InteractionInstance` from an instance of a class.

The name of the `InteractionInstance` will be taken from the name of the implementing `interface` (Java) or `trait` (Scala) 
(it must match the name of the `Interaction` at the `Recipe`).

The interface MUST declare a public method called `apply`, and the types must match those of the expected provided ingredients.

Notice that his function might throw an exception if the instance is not correctly done (this is why in Scala the API is
named "unsafe").

```scala tab="Scala"
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

sealed trait ReserveItemsOutput
case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput
case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

trait ReserveItems {

  def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput]
}

class ReserveItemsInstance extends ReserveItems {

  override def apply(orderId: String, items: List[String]): Future[ReserveItemsOutput] = {

    // Http call to the Warehouse service
    val response: Future[Either[List[String], List[String]]] =
    // This is mocked for the sake of the example
      Future.successful(Right(items))

    // Build an event instance that Baker understands
    response.map {
      case Left(unavailableItems) =>
        OrderHadUnavailableItems(unavailableItems)
      case Right(reservedItems) =>
        ItemsReserved(reservedItems)
    }
  }
}

val reserveItemsInstance: InteractionInstance =
  InteractionInstance.unsafeFrom(new ReserveItemsInstance)
```

``` java tab="Java"
import com.ing.baker.runtime.javadsl.InteractionInstance;
import com.ing.baker.runtime.javadsl.Interaction;

/** Java interface used for the Recipe */
public interface ReserveItems extends Interaction {

    interface ReserveItemsOutcome {}

    class OrderHadUnavailableItems implements ReserveItemsOutcome {

        public final List<String> unavailableItems;

        public OrderHadUnavailableItems(List<String> unavailableItems) {
            this.unavailableItems = unavailableItems;
        }
    }

    class ItemsReserved implements ReserveItemsOutcome {

        public final List<String> reservedItems;

        public ItemsReserved(List<String> reservedItems) {
            this.reservedItems = reservedItems;
        }
    }

    @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
    ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("items") List<String> items);
}

/** Implementation of the interface used for creating an InteractionInstance */
public class ReserveItems implements JWebshopRecipe.ReserveItems {

    // The body of this method is going to be executed by the Baker runtime when the ingredients are available.
    @Override
    public ReserveItemsOutcome apply(String id, List<String> items) {
        return new ReserveItems.ItemsReserved(items);
    }
}
        
/** Create an InteractionInstance from an instance of the ReserveItems implementation */        
InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());
```

## baker.addInteractionInstance(interactionInstance)

The Baker runtime requires you to add all `InteractionInstances` before adding any related `CompiledRecipes`. This can
be done using the `baker.addInteractionInstance(interactionInstance)` or the `baker.addInteractionInstances(intance1, instance2, ...)`
APIs.

_Note: in Java the api returns a `CompletableFuture<BoxedUnit>`, this is because the API is implemented in Scala, so 
Scala's `Unit` get translated to `BoxedUnit`, but you should you ignore it and consider it as good as Java's `void`,
except it comes in a `CompletableFuture` that will help you handle async programming._

```scala tab="Scala"

val baker: Baker = Baker.akkaLocalDefault(actorSystem, materializer)

val reserveItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(new ReserveItems())

val result: Future[Unit] = baker.addInteractionInstance(reserveItemsInstance)

```

```java tab="Java"

Baker baker = Baker.akkaLocalDefault(actorSystem, materializer);

InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());

CompletableFuture<BoxedUnit> = baker.addInteractionInstance(reserveItemsInstance);

```

## RecipeCompiler.compile(recipe)

`Recipes` once built must be converted into a data structure called `CompiledRecipe` that helps a `RecipeInstances` 
to understand, store and run your process. These can be used to create a new `RecipeInstance` from a `baker` 
runtime that contains both a `CompiledRecipe` and the required `InteractionInstances`, or they can as well be converted
into a [visualziation](visualization.md).

```scala tab="Scala"
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe

val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
```

```java tab="Java"
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;

CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
```

## baker.addRecipe(compiledRecipe)

Once `Recipes` have been transformed into `CompiledRecipes` they must be added to a baker runtime. The `baker.addRecipe(compiledRecipe)`
API will do so and return an id that you can use to reference the added recipe later on.

_Note: Before doing this, baker requires you to add all related `InteractionInstance` to the runtime, because it 
does validation regarding this to ensure that every recipe is actually runnable because it doe not lack any `InteractionInstance`._

```scala tab="Scala"
val recipeId Future[String] = baker.addRecipe(compiledRecipe)
```

```java tab="Java"
CompletableFuture<String> recipeId = baker.addRecipe(compiledRecipe);
```

## baker.getAllRecipes()

The baker at runtime can give you a map of all the currently available recipes that has been previously added to Baker.

```scala tab="Scala"
import com.ing.baker.runtime.scaladsl.RecipeInformation
import scala.concurrent.Future

val allRecipes: Future[Map[String, RecipeInformation]] = baker.getAllRecipes
```

```java tab="Java"
import com.ing.baker.runtime.javadsl.RecipeInformation;
import java.util.concurrent.CompletableFuture;
import java.util.Map;

CompletableFuture<Map<String, RecipeInformation>> allRecipe = baker.getAllRecipes();
```

## baker.bake(recipeId, recipeInstanceId)

Once the Baker runtime contains a `CompiledRecipe` and all the associated `InteractionInstances` then you can use the 
`baker.bake(recipeId, recipeInstanceId)` API to create a `RecipeInstance` that will contain the state of your process
and execute any `InteractionInstance` as soon as all its required `InteractionIngredients` are available.
 
_Note: This API requires you to choose a `recipeInstanceId`, the API does not provide one for you, this is so that 
you can manage this reference as required._

_Note: in Java the api returns a `CompletableFuture<BoxedUnit>`, this is because the API is implemented in Scala, so 
Scala's `Unit` get translated to `BoxedUnit`, but you should you ignore it and consider it as good as Java's `void`,
except it comes in a `CompletableFuture` that will help you handle async programming._

```scala tab="Scala"
val program: Future[Unit] = for {
  _ <- baker.addInteractionInstance(interactionInstances)
  recipeId <- baker.addRecipe(compiledRecipe)
  recipeInstanceId = "my-id"
  _ <- baker.bake(recipeId, recipeInstanceId)
} yield ()
```

```java tab="Java"
String recipeInstanceId = "my-id";
CompletableFuture<BoxedUnit> result = baker.addInteractionInstace(reserveItemsInstance)
    .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
    .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId));
```

## EventInstance.from(object)

As part of our efforts to ease the creation of 

## baker.fireEvent(recipeInstanceId, eventInstance)

## baker.getRecipeInstanceState(recipeInstanceId)

## baker.getAllInteractionInstancesMetadata()

## baker.getVisualState(recipeInstanceId, style)

## baker.registerEventListener(recipeName, listenerFunction)

## baker.registerBakerEventListener(listenerFunction)

## baker.retryInteraction(recipeInstanceId, interactionName)

## baker.resolveInteraction(recipeInstanceId, interactionName, event)

## baker.stopRetryingInteraction(recipeInstanceId, interactionName)






```scala tab="Scala"
```

```java tab="Java"
```
______________________________________

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

In our [webshop example](index.md#visual-representation) the first events that can happen are `OrderPlaced`, `PaymentMade` and `CustomerInfoReceived`.

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

