# Design a Recipe

Before creating a recipe, we have to translate the business requirements into Baker's three essential building blocks:
`Ingredients`, `Events`, and `Interactions`.

Ingredients are immutable containers for the data in your process. In this example, `orderId` and the list of
`productIds` both qualify as an ingredient. Ingredients serve as input for interactions and are carried through
the process via events.

Events represent something that has happened in your process. Most of the time, events are outputs of interactions.
Sometimes events come from outside the process. Those events are called `SensoryEvents`. SensoryEvents are used
to start/trigger the process.

An interaction resembles a function. It requires inputs (ingredients) and provides output (events). This means an
interaction can do many things. For example, you can have interactions that fetch data from another service, or
an interaction that sends a message to an event broker, etc.

## Ingredients and Events

A recipe is always triggered by a sensory event. In this web-shop example we can model the placing of the order
as the sensory event. This event will provide the two required ingredients: `orderId` and a list of `productIds`.

=== "Java"

    ```java 
    
    public class OrderPlaced {
        public final String orderId;
        public final List<String> items;
    
        public OrderPlaced(String orderId, List<String> items) {
            this.orderId = orderId;
            this.items = items;
        }
    }
    ```

=== "Kotlin"

    ```kotlin

    data class OrderPlaced(
        val orderId: String,
        val productIds: List<String>
    )
    ```

=== "Scala"

    ```scala 

    import com.ing.baker.recipe.scaladsl._

    object Ingredients {

        val OrderId: Ingredient[String] =
          Ingredient[String]("orderId")

        val ProductIds: Ingredient[List[String]] =
          Ingredient[List[String]]("items")
    }

    object Events {

        val OrderPlaced: Event = Event(
          name = "OrderPlaced",
          providedIngredients = Seq(
            Ingredients.OrderId,
            Ingredients.ProductIds
          ),
          maxFiringLimit = Some(1)
        )
    }
    ```

Ingredients and events are just data structures that describe your process data. In this example `OrderPlaced` is an
event which carries two ingredients: `orderId` and `productIds`. An ingredient consists of a name and
type information. For example for the field `String orderId`, Baker creates an ingredient with the name of "orderId" 
and a type of `CharArray`. More information about Baker types can be found in [this section](../../reference/baker-types-and-values/).

As shown in the Scala example, events have a maximum amount of times they are allowed to fire. The Baker runtime will 
enforce this limit. For more information about this and other features of events please refer to [this section](../../reference/dsls/#events).

## Interactions

Next, it's time to model our interaction. In our example it's just a simple call to the warehouse service to reserve
the items.

_Note: Notice that when using the reflection API, the Java/Kotlin interface or Scala trait that will represent your interaction
must have a method named `apply`, this is the method that the reflection API will convert into Baker
types/ingredients/events._

=== "Java"

    ```java

    public class JWebshopRecipe {
        
        // ... previous event
        
        // Interface that will represent our Interaction, notice that it is declaring inner events.
        
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

            // The @FireEvent annotation communicates the reflection API about several possible outcome events.
            @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
            // The @RequiresIngredient annotation communicates the reflection API about the ingredient names that other events
            // must provide to execute this interaction.
            // The method MUST be named `apply`
            ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("productIds") List<String> productIds);
        }
        
    }

    ```

=== "Kotlin"

    ```kotlin
    interface ReserveItems : Interaction {

        sealed interface ReserveItemsOutcome
        data class OrderHadUnavailableItems(val unavailableItems: List<String>) : ReserveItemsOutcome
        data class ItemsReserved(val reservedItems: List<String>) : ReserveItemsOutcome
    
        fun apply(orderId: String, productIds: List<String>): ReserveItemsOutcome
    }

    ```

=== "Scala"

    ```scala 

    object Interactions {
        
        val ReserveItems: Interaction = Interaction(
              name = "ReserveItems",
              inputIngredients = Seq(
                Ingredients.OrderId,
                Ingredients.ProductIds,
              ),
              output = Seq(
                Events.OrderHadUnavailableItems,
                Events.ItemsReserved
              )
            )
    }

    object Ingredients {

        // ... previous ingredients
        
        val ReservedItems: Ingredient[List[String]] =
          Ingredient[List[String]]("reservedItems")

        val UnavailableItems: Ingredient[List[String]] =
          Ingredient[List[String]]("unavailableItems")
    }

    object Events {

        // ... previous events
        
        val OrderHadUnavailableItems: Event = Event(
          name = "OrderHadUnavailableItems",
          providedIngredients = Seq(
            Ingredients.UnavailableItems
          ),
          maxFiringLimit = Some(1)
        )

        val ItemsReserved: Event = Event(
          name = "ItemsReserved",
          providedIngredients = Seq(
            Ingredients.ReservedItems
          ),
          maxFiringLimit = Some(1)
        )
    }

    ```

## The Recipe

The final step is to create the "blueprint" of our process: the recipe. To define a recipe you can use the Java,
Kotlin, or Scala DSL.

=== "Java"

    ```java

    public class JWebshopRecipe {

        // ... previous events and interactions.

        public final static Recipe recipe = new Recipe("WebshopRecipe")
                .withSensoryEvents(OrderPlaced.class)
                .withInteractions(of(ReserveItems.class));
    }
    ```

=== "Kotlin"
    ```kotlin

    object WebShopRecipe {
        val recipe = recipe("web-shop reserve items recipe") {
            sensoryEvents {
                event<OrderPlaced>()
            }
            interaction<ReserveItems>()
        }
    }

    ```

=== "Scala"

    ```scala 

    object WebshopRecipe {
      val recipe: Recipe = Recipe("Webshop")
        .withSensoryEvents(
          Events.OrderPlaced
        )
        .withInteractions(
          Interactions.ReserveItems,
        )
    }
    ```

Despite this simple example, you might have realised that this can be further composed into bigger processes by
making new interactions that require events and ingredients which are outputs of previous interactions. You can also 
create interactions which take no input ingredients but are executed after certain events are fired. For this and other 
features please refer to the full DSL documentation [here](../../reference/dsls/#events).

It should come as no surprise that this setup allows `Ingredients`, `Events` and `Interactions` to  be reused in different 
Recipes. Giving common business verbs that your programs and organisation can use across teams, the same way different 
cooking recipes share processes (simmering, boiling, cutting).

## Scala reflection API

As you went through the examples you might have found the Scala API quite verbose. This is because the Java and Kotlin
APIs lean on reflection. We also have a Scala reflection API available, resulting in more concise Scala recipe
definitions.

=== "Scala (Reflection API)"

    ```scala 

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
          Event[OrderPlaced])
        .withInteractions(
          ReserveItems)
    }

    ```