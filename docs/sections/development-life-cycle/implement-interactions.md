# Implement Interactions

After creating a recipe, and before we can even run processes from it, we need to create `InteractionInstances` that the
Baker runtime will use to execute the real actions of the recipe, these instances must match the `Interactions` in the `Recipe`,
that means that the name and the input types must match. 

For the Scala DSL you need to create an object of `InteractionImplementation`, or use the reflection API.

For the Java DSL you need to implement the interface with the `apply` method that you used for the `Interaction` in the `Recipe` 
and then use the `InteractionImplementation.from(new Implementation())` reflection API, this will create a new `InteractionImplementation`
that we will later on add to a baker runtime.

``` scala tab="Scala"
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
    // The body of this function is going to be executed by the Baker runtime when the ingredients are available.
    // ListValue and PrimitiveValue are used in the body
```

``` scala tab="Scala Reflection API"
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global

trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
}

val reserveItemsInstance: InteractionInstance = InteractionInstance.unsafeFrom(
    new ReserveItems {

        def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] = {

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
)
```

``` java tab="Java"
import com.ing.baker.runtime.javadsl.InteractionInstance;

public class ReserveItems implements JWebshopRecipe.ReserveItems {

    // The body of this method is going to be executed by the Baker runtime when the ingredients are available.
    @Override
    public ReserveItemsOutcome apply(String id, List<String> items) {
        return new JWebshopRecipe.ReserveItems.ItemsReserved(items);
    }
}
        
        
InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());
```
