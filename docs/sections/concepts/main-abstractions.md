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

``` scala tab="Scala"
import com.ing.baker.types._

val data: (Type, Value) = (Int32, PrimitiveValue(42))
```

``` java tab="Java"
import com.ing.baker.types.*;

Type dataType = Int32$.MODULE$;
Value dataValue = PrimitiveValue.apply(42);
```

Full documentation about the type system can be found [here]().

## Ingredient and IngredientInstance

`Ingredients` are _pure data_, This data is **immutable**, which means that it can only be created and never 
mutated through the process. And there is **no subtyping** or hierarchy. 

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
// In Java Ingredients are extracted from a class 
// representing an Event by using java reflection.
// See the full example at the "Recipe and RecipeInstance" section
```

They are carried through your process within events, and are inputs for interactions.

## Event and EventInstance

`Events` represent happenings in your process that might carry `Ingredient`s, they represent an "asynchronous boundary",
they are always either output from `Interaction`s or a special case called `SensoryEvent`s; we call sensory events to the 
events that come from "outside" of your recipe and are normally used to start your process.

For a `Recipe` there exist `Event`s which are a name, a set of `Ingredient`s and a maximum amount of firings; the 
`maxFiringLimit` is a property which describes the number of times an event is allowed to fire, this is later on
enforced by the Baker runtime. To know more about firing limits and all the other configurable properties, please 
refer to the [DSLs documentation]().

__Note: Names of sensory `Event` and `EventInstance` must match, so that Baker can correctly execute your process flow.__

For a `RecipeInstance` there exist `EventInstance`s which are a (TODO)

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

val FirstOrderPlaced: EventInstance = EventInstance(
  name = "OrderPlaced",
  providedIngredients = Map(
    "orderId" -> PrimitiveValue("uuid-0123456789"),
    "items" -> ListValue(List(PrimitiveValue("item1-id"), PrimitiveValue("item2-id")))
  )
)
```

``` java tab="Java"
// In Java Events and EventInstances are extracted from a 
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

To fire a `SensoryEvent` use the `bakerRuntime.fireEvent(recipeInstanceId, event)` API variations, for full documentation 
on these, please refer to [this section]().

``` scala tab="Scala"
```

``` java tab="Java"
```

## Interaction and InteractionInstance

## Recipe and RecipeInstance