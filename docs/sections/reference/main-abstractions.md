# Main Abstractions

Baker makes a strong division between the specification of your business process and the runtime implementations.

| Specification | Runtime |
|---------------|---------|
| `Type` | `Value` |
| `Ingredient` | `IngredientInstance` |
| `Event` | `EventInstance` |
| `Interaction` | `InteractionInstance` |
| `Recipe` | `RecipeInstance` |

The first four are used to create `Recipe`s which serve as "blueprints" of your process. In the Baker
runtime they are used within `RecipeInstance`s, which are created from a `Recipe` specification to execute the flow of 
your process.

## Type and Value

Because of the distributed nature of Baker and how the runtime works, we need to have serializable types and values to 
transfer recipes and data between nodes and to match over such data, that is why we implemented a type system on top of Scala.
They help not just to model your domain, but also for Baker to identify when to execute interactions. 

If you are using all of our reflection APIs then you will not use them directly, but it is good to know of their 
existence.

Full documentation about the type system can be found [here](../../reference/baker-types-and-values/).

``` scala tab="Scala"
import com.ing.baker.types._

val data: (Type, Value) = (Int32, PrimitiveValue(42))
```

``` java tab="Java"
import com.ing.baker.types.*;

Type dataType = Int32$.MODULE$;
Value dataValue = PrimitiveValue.apply(42);
```

## Ingredient and IngredientInstance

`Ingredients` are containers for the data in your process. This data is **immutable**, which means that it can only be created and never 
changes in the process. There is **no subtyping**, nor hierarchy. `Ingredients` are carried through your process 
with `Events`, and are inputs for `Interactions`.

For a `Recipe` there exist `Ingredients` which are a name and a `Type`, they are used to model the data of your process.

For a `RecipeInstance` there exist `IngredientInstance`s, which are a name and a `Value`, they are used to move data 
through your process. 

``` scala tab="Scala"
import com.ing.baker.recipe.scaladsl.Ingredient

val OrderId: Ingredient[String] =
    Ingredient[String]("orderId")
    

import com.ing.baker.runtime.scaladsl.IngredientInstance

val orderIdInstance: IngredientInstance = 
    IngredientInstance("orderId", PrimitiveValue("uuid-123456789"))
```

``` java tab="Java"
// In Java, Ingredients are extracted from a class 
// representing an Event by using java reflection.
// See the full example at the "Recipe and RecipeInstance" section
```

## Event and EventInstance

`Events` represent happenings in your process that might carry `Ingredients`, they represent an "asynchronous boundary",
they are always either output from `Interactions` or a special case called `SensoryEvent`s; we call sensory events to the 
events that come from "outside" of your recipe and are normally used to start your process.

For a `Recipe` there exist `Events` which are a name, a set of `Ingredients` and a maximum amount of firings; the 
`maxFiringLimit` is a property which describes the number of times an event is allowed to fire, this is later on
enforced by the Baker runtime. To know more about firing limits and all the other configurable properties, please 
refer to the [DSLs documentation](../../reference/dsls/).

For a `RecipeInstance` there exist `EventInstance`s which are data structures that must match their interface equivalent
declared as `Events` on the `Recipe`. They notify a baker `RecipeInstance` of an actual happening and may carry `Ingredient`
values; the baker `RecipeInstance` will then use available `Ingredients` to execute `InteractionInstance`s.

__Note: Names of sensory `Event` and `EventInstance` must match, so that Baker can correctly execute your process flow.__

``` scala tab="Scala"
/** Event */
import com.ing.baker.recipe.scaladsl.Event
import com.ing.baker.recipe.scaladsl.Ingredient

val OrderPlaced: Event = Event(
  name = "OrderPlaced",
  providedIngredients = Seq(
    Ingredient[String]("orderId"),
    Ingredient[List[String]]("items")
  ),
  maxFiringLimit = Some(1)
)

/** EventInstance */
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.types.{PrimitiveValue, ListValue}

val firstOrderPlaced: EventInstance = EventInstance(
  name = "OrderPlaced",
  providedIngredients = Map(
    "orderId" -> PrimitiveValue("uuid-0123456789"),
    "items" -> ListValue(List(PrimitiveValue("item1-id"), PrimitiveValue("item2-id")))
  )
)
```

``` java tab="Java"
// In Java, Events and EventInstances are extracted from a 
// class by using java reflection.
// Please check the full recipe example below on the 
// Recipe and RecipeInstance subsection
    
import com.ing.baker.runtime.javadsl.EventInstance;

public static class OrderPlaced {

    public final String orderId;
    public final List<String> items;

    public OrderPlaced(String orderId, List<String> items) {
        this.orderId = orderId;
        this.items = items;
    }
}

List<String> items = new ArrayList<>(2);
items.add("item1");
items.add("item2");
OrderPlaced order1 = new OrderPlaced("uuid-0123456789", items);
EventInstance order1Event = EventInstance.from(order1);

```

To fire a `SensoryEvent` use the `bakerRuntime.fireEvent(recipeInstanceId, event)` API variations, 
after creating the baker runtime, adding your recipe to the runtime and `baking` a `RecipeInstance`. For full 
documentation on this please refer to the [runtime documentation](../../reference/runtime/).

``` scala tab="Scala"
import akka.actor.ActorSystem
import com.ing.baker.runtime.common.EventResult
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

import scala.concurrent.Future

implicit val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
val baker: Baker = Baker.akkaLocalDefault(actorSystem)

// This example is using the reflection API `EventInstance.unsafeFrom`
val FirstOrderPlaced: EventInstance = EventInstance
    .unsafeFrom(OrderPlaced("order-uuid", List("item1", "item2")))
val recipeInstanceId: String = "recipe id from previously baked recipe instance"

val result: Future[EventResult] = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, FirstOrderPlaced)
```

``` java tab="Java"
import akka.actor.ActorSystem;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventResult;

import java.util.concurrent.CompletableFuture;

ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Baker baker = Baker.akkaLocalDefault(actorSystem);

String recipeInstanceId = "recipe id from previously baked recipe instance";
List<String> items = new ArrayList<>(2);
items.add("item1");
items.add("item2");
EventInstance firstOrderPlaced = 
        EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));

CompletableFuture<EventResult> result = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced);
```

## Interaction and InteractionInstance

An interaction resemblance a function, it requires input (`Ingredients`) and provides output (`Events`). Within this
contract it may do anything. For example:

* Query a microservice
* Send messages to an event broker like Kafka
* Await for a message from an event broker
* Generate a file
* Do transformations on the ingredients (we like to call these interactions `Sieves`)

For a `Recipe` there exist `Interactions` which are a name, a sequence of `Ingredients` describing all the input (all of),
and a sequence of `Events` describing the _possible_ event outputs (one of). At the recipe level there are several more 
specifics that can be configured, like requiring events without ingredients, adding predefined ingredients, overriding
ingredient names, or handling unexpected failure, for these please refer to the [DSLs documentation](../../reference/dsls/).

For a `RecipeInstance` there exist `InteractionInstance`s which are a name, an input type description, and an implementation
of a method/function that will be called when the interaction is executed. The input name and the input type description 
is used by the Baker runtime to find the correct `InteractionImplementation` to execute when the `Ingredients` are available.

__Note: Names of sensory `Event` and `EventInstance` must match, so that Baker can correctly execute your process flow.__

__Note: For asynchronous programming, the Scala DSL `InteractionInstance` can return a `Future[A]` and the Java DSL can
return a `CompletableFuture<A>`, and the Baker runtime will handle the async results of the instances.__

``` scala tab="Scala"
/** Interaction */
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}

val ReserveItems: Interaction = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
        Ingredient[String]("orderId"),
        Ingredient[List[String]]("items")
    ),
    output = Seq(
        Events.OrderHadUnavailableItems,
        Events.ItemsReserved
    )
)

/** InteractionInstance */
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.types.{CharArray, ListType, ListValue, PrimitiveValue}

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

val ReserveItemsInstance = InteractionInstance(
    name = ReserveItems.name,
    input = Seq(CharArray, ListType(CharArray))
    run = handleReserveItems
)

def handleReserveItems(input: Seq[IngredientInstance]): Future[Option[EventInstance]] = ???
    // ListValue and PrimitiveValue are used in the body
```

``` java tab="Java"
/** Interaction */
import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

public interface ReserveItems extends Interaction {

    interface ReserveItemsOutcome {
    }

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

    // Annotations are needed for wiring ingredients and validating events.
    @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
    // The name of the method must be "apply" for the reflection API to work.
    // This method can also return a `CompletableFuture<ReserveItemsOutcome>` for asynchronous programming.
    ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("items") List<String> items);
}

/** InteractionInstance */
import com.ing.baker.runtime.javadsl.InteractionInstance;

public class ReserveItems implements JWebshopRecipe.ReserveItems {

    @Override
    public ReserveItemsOutcome apply(String id, List<String> items) {
        return new JWebshopRecipe.ReserveItems.ItemsReserved(items);
    }
}
```

```scala tab="Scala (Reflection API)"
// See the DSLs documentation for more on the reflection API
trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
}

class ReserveItemsInstance extends ReserveItems {

  override def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] = {

    // Http call to the Warehouse service
    val response: Future[Either[List[String], List[String]]] =
    // This is mocked for the sake of the example
      Future.successful(Right(items))

    // Build an event instance that Baker understands
    response.map {
      case Left(unavailableItems) =>
        WebshopRecipeReflection.OrderHadUnavailableItems(unavailableItems)
      case Right(reservedItems) =>
        WebshopRecipeReflection.ItemsReserved(reservedItems)
    }
  }
}

val reserveItemsInstance: InteractionInstance =
  InteractionInstance.unsafeFrom(new ReserveItemsInstance)
```

After creating your `InteractionInstance`s, you need to add them to the baker runtime so that Baker can match them to the `Interactions`
of your `Recipe` and call them when needed.

``` scala tab="Scala"
import akka.actor.ActorSystem
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Future

val done: Future[Unit] = baker.addInteractionInstance(reserveItemsInstance)
```

``` java tab="Java"
import akka.actor.ActorSystem;
import com.ing.baker.runtime.javadsl.Baker;

import scala.runtime.BoxedUnit;
import java.util.concurrent.CompletableFuture;

ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Baker baker = Baker.akkaLocalDefault(actorSystem);

CompletableFuture<BoxedUnit> done = baker.addInteractionInstance(reserveItemsInstance);
```

## Recipe and RecipeInstance

All you `Ingredients`, `Events` and `Interactions` must be added to a single unit called the `Recipe`, which works as the
"blueprint" of your precess.

```scala tab="Scala"
import com.ing.baker.recipe.scaladsl.Recipe

val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
        Events.OrderPlaced
    )
    .withInteractions(
        Interactions.ReserveItems,
    )
```

```scala tab="Scala Full Example"
package webshop

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

object WebshopRecipeReflection {

  case class OrderPlaced(orderId: String, items: List[String])

  sealed trait ReserveItemsOutput

  case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

  case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

  val ReserveItems = Interaction(
    name = "ReserveItems",
    inputIngredients = Seq(
      Ingredient[String]("orderId"),
      Ingredient[List[String]]("items")
    ),
    output = Seq(
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
  )

  val recipe: Recipe = Recipe("Webshop")
    .withSensoryEvents(
      Event[OrderPlaced],
      Event[OrderHadUnavailableItems],
      Event[ItemsReserved]
    )
    .withInteractions(
      ReserveItems
    )
}


```

```java tab="Java"
import com.ing.baker.recipe.javadsl.Recipe;
import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

public final static Recipe recipe = new Recipe("WebshopRecipe")
        .withSensoryEvents(OrderPlaced.class)
        .withInteractions(of(ReserveItems.class));
```

```java tab="Java Full Example"
package webshop;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.Recipe;

import java.util.List;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

public class JWebshopRecipe {

    public static class OrderPlaced {

        public final String orderId;
        public final List<String> items;

        public OrderPlaced(String orderId, List<String> items) {
            this.orderId = orderId;
            this.items = items;
        }
    }

    public interface ReserveItems extends Interaction {

        interface ReserveItemsOutcome {
        }

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

    public final static Recipe recipe = new Recipe("WebshopRecipe")
        .withSensoryEvents(OrderPlaced.class)
        .withInteractions(of(ReserveItems.class));
}

```

A recipe must be added to a baker runtime so that you can create "bake" a `RecipeInstance` from it. For that it must be
first "compiled" by using the provided compiler.

Here is a full example of creating a baker runtime, adding the `InteractionInstances` and the compiled `Recipe` (order matters
becase baker validates that all recipes have valid implementations when added), and firing an `Event` that will execute 
the `Interaction`

```scala tab="Scala"
import akka.actor.ActorSystem
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

implicit val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
val baker: Baker = Baker.akkaLocalDefault(actorSystem)

val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)

val program: Future[Unit] = for {
    _ <- baker.addInteractionInstance(WebshopInstances.ReserveItemsInstance)
    recipeId <- baker.addRecipe(compiledRecipe)
    _ <- baker.bake(recipeId, "first-instance-id")
    firstOrderPlaced: EventInstance =
        EventInstance.unsafeFrom(WebshopRecipeReflection.OrderPlaced("order-uuid", List("item1", "item2")))
    result <- baker.fireEventAndResolveWhenCompleted("first-instance-id", firstOrderPlaced)
} yield assert(result.events == Seq(
    WebshopRecipe.Events.OrderPlaced.name,
    WebshopRecipe.Events.ItemsReserved.name
))
```

```java tab="Java"
import akka.actor.ActorSystem;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventResult;
import com.ing.baker.runtime.javadsl.InteractionInstance;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;


ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Baker baker = Baker.akkaLocalDefault(actorSystem);

List<String> items = new ArrayList<>(2);
items.add("item1");
items.add("item2");
EventInstance firstOrderPlaced =
        EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));

InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());
CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

String recipeInstanceId = "first-instance-id";
CompletableFuture<List<String>> result = baker.addInteractionInstance(reserveItemsInstance)
    .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
    .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
    .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
    .thenApply(EventResult::events);

List<String> blockedResult = result.join();
assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("ReservedItems"));
```
