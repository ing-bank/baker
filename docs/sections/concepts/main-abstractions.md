# Main Abstractions

Baker makes a strong division between the specification of your business process and the runtime implementations.

| Specification | Runtime |
|---------------|---------|
| `Type` | `Value` |
| `Ingredient` | `IngredientInstance` |
| `Event` | `EventInstance` |
| `Interaction` | `InteractionInstance` |
| `Recipe` | `RecipeInstance` |

The first 4 are used to create `Recipe`s which serve as "blueprints" of your process. And in the Baker
runtime they are used within `RecipeInstance`s, which are created from a `Recipe` specification to execute the flow of 
your process.

## Type and Value

Because of the distributed nature of Baker and how the runtime works, we need to have serializable types and values to 
transfer recipes and data between nodes and to match over such data, that is why we implemented a type system on top of Scala.
They help not just to model your domain but also for Baker to identify when to execute interactions. 

If you are using all of our reflection APIs then you will not use them directly, but it is good to know of their 
existence.

Full documentation about the type system can be found [here]().

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

`Ingredient`s are _pure data_, This data is **immutable**, which means that it can only be created and never 
mutated through the process. And there is **no subtyping** or hierarchy. `Ingredient`s are carried through your process 
within `Event`s, and are inputs for `Interaction`s.

For a `Recipe` there exist `Ingredient`s which are a name and a `Type`, they are used to model the data of your process.

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

`Events` represent happenings in your process that might carry `Ingredient`s, they represent an "asynchronous boundary",
they are always either output from `Interaction`s or a special case called `SensoryEvent`s; we call sensory events to the 
events that come from "outside" of your recipe and are normally used to start your process.

For a `Recipe` there exist `Event`s which are a name, a set of `Ingredient`s and a maximum amount of firings; the 
`maxFiringLimit` is a property which describes the number of times an event is allowed to fire, this is later on
enforced by the Baker runtime. To know more about firing limits and all the other configurable properties, please 
refer to the [DSLs documentation]().

For a `RecipeInstance` there exist `EventInstance`s which are data structures that must match their interface equivalent
declared as `Event`s on the `Recipe`. They notify a baker `RecipeInstance` of an actual happening and may carry `Ingredient`
values; the baker `RecipeInstance` will then use available `Ingredient`s to execute `InteractionInstance`s.

__Note: Names of sensory `Event` and `EventInstance` must match, so that Baker can correctly execute your process flow.__

``` scala tab="Scala"
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
    public final String[] items;

    public OrderPlaced(String orderId, String[] items) {
        this.orderId = orderId;
        this.items = items;
    }
}

String[] items = {"item1", "item2"};
OrderPlaced order1 = new OrderPlaced("uuid-0123456789", items);
EventInstance order1Event = EventInstance.from(order1);

```

To fire a `SensoryEvent` use the `bakerRuntime.fireEvent(recipeInstanceId, event)` API variations, 
after creating the baker runtime, adding your recipe to the runtime and `baking` a `RecipeInstance`. For full 
documentation on this please refer to the [runtime documentation]().

``` scala tab="Scala"
import java.util.concurrent.Future

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.common.EventResult
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

implicit val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
implicit val materializer: Materializer =
    ActorMaterializer()
val baker: Baker = Baker.akkaLocalDefault(actorSystem, materializer)

// This example is using the reflection API `EventInstance.unsafeFrom`
val FirstOrderPlaced: EventInstance = EventInstance
    .unsafeFrom(OrderPlaced("order-uuid", List("item1", "item2")))
val recipeInstanceId: String = "recipe id from previously baked recipe instance"

val result = Future[EventResult] = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, FirstOrderPlaced)
```

``` java tab="Java"
import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventResult;

import java.util.concurrent.CompletableFuture;

ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Materializer materializer = ActorMaterializer.create(actorSystem);
Baker baker = Baker.akkaLocalDefault(actorSystem, materializer);

String recipeInstanceId = "recipe id from previously baked recipe instance";
String[] items = {"item1", "item2"};
EventInstance firstOrderPlaced = 
        EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));

CompletableFuture<EventResult> result = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced);
```

## Interaction and InteractionInstance

An interaction resemblance a function, it requires input (`Ingredient`s) and provides output (`Event`s). Within this
contract it may do anything. For example:

* Query a microservice
* Send messages to an event broker like Kafka
* Await for a message from an event broker
* Generate a file
* Do transformations on the ingredients (we like to call these interactions `Sieves`)

For a `Recipe` there exist `Interaction`s which are a name, a sequence of `Ingredient`s describing all the input (all of),
and a sequence of `Event`s describing the _possible_ event outputs (one of). At the recipe level there are several more 
specifics that can be configured, like requiring events without ingredients, adding predefined ingredients, or overriding
ingredient names, for these please refer to the [DSLs documentation]().

For a `RecipeInstance` there exist `InteractionInstance`s which are a name, 

## Recipe and RecipeInstance