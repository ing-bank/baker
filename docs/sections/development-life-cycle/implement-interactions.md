# Implement Interactions

Before we can run our recipe, we need to create `InteractionInstances` that the Baker runtime will use to execute the
interactions. In other words, we need to provide implementations for the interactions.

=== "Java"

    ```java 
    public class ReserveItemsInstance implements ReserveItems {

        // The body of this method is going to be executed by the Baker runtime when the ingredients are available.
        @Override
        public ReserveItemsOutcome apply(String id, List<String> productIds) {
            // Add your implementation here.
            // The body of this function is going to be executed by the Baker runtime when the ingredients are available.
        }
    }
    ```

=== "Kotlin"

    ```kotlin
    class ReserveItemsInstance : ReserveItems {
        override fun apply(orderId: String, productIds: List<String>): ReserveItemsOutcome {
            // Add your implementation here.
            // The body of this function is going to be executed by the Baker runtime when the ingredients are available.
        }
    }
    ```

=== "Scala Reflection API"

    ```scala 
    import com.ing.baker.runtime.scaladsl.InteractionInstance

    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global

    class ReserveItemsInstance extends ReserveItems {

        override def apply(orderId: String, productIds: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] = {
            // Add your implementation here.
            // The body of this function is going to be executed by the Baker runtime when the ingredients are available.
        }
    }
    ```

=== "Scala"

    ```scala 
    import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
    import com.ing.baker.types.{CharArray, ListType, ListValue, PrimitiveValue}

    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global

    val ReserveItemsInstance = InteractionInstance(
        name = ReserveItems.name,
        input = Seq(CharArray, ListType(CharArray))
        run = handleReserveItems
    )

    def handleReserveItems(input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
        // Add your implementation here.
        // The body of this function is going to be executed by the Baker runtime when the ingredients are available.
    }
    ```
