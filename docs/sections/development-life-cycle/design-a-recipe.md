# Design a Recipe

_Full project examples including tests and configuration can be found [here](https://github.com/ing-bank/baker/tree/master/examples)._

The _Development Life Cycle_ section provides a "top-down"/"by-example" guide to baker, all of the concepts 
are introduced through exemplification on hypothetical development situations.

## Modeling the order placement process for a webshop using Ingredients, Events and Recipes.

The recipe DSL allows you to declaratively describe your business process. The design always starts with the
business requirements, lets say you are developing a webshop which will have many different microservices on 
the backend. The initial requirements for the order reservation process reads: 

_"An order contains an order id and a list of store item identifiers, when an order is placed it must first 
be validated by reserving the items from the warehouse service, a success scenario yields the ids of the 
reserved items, but if at least one item is unavailable at the warehouse a failure yields the list of unavailable items 
and the process stops"_

When developing with Baker we must first translate the requirements into our 3 essential building blocks, 
`Ingredients` for raw data, `Events` for happenings (that might contain ingredients), and `Interactions` which 
have ingredients as input, execute actions with other systems, and yield more events. We will do this so that the 
baker runtime can orchestrate the execution of our process through the underlying microservices.

## Ingredients and Events

A recipe always starts with initial events, also called `Sensory Events`, in the case of our first requirement 
we could model the placing of an order as an event, which will provide 2 ingredients: the order id and the list
of items.

``` scala tab="Scala"

import com.ing.baker.recipe.scaladsl._

object Ingredients {

    val OrderId: Ingredient[String] =
      Ingredient[String]("orderId")

    val Items: Ingredient[List[String]] =
      Ingredient[List[String]]("items")
}

object Events {

    val OrderPlaced: Event = Event(
      name = "OrderPlaced",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )
}

```

``` java tab="Java"

// In Java the data structures to represent Events and Ingredients 
// will be extraxted from a class by the reflection API when building 
// the Recipe. (see below for full example)

public class JWebshopRecipe {

    public static class OrderPlaced {

        public final String orderId;
        public final List<String> items;

        public OrderPlaced(String orderId, List<String> items) {
            this.orderId = orderId;
            this.items = items;
        }
    }
}

```

Depending on your programming language, you might want to import the corresponding dsl, i.e. `scaladsl` vs `javadsl`.

Ingredients and events are just data structures that describe your process data, carrying not just the names, but
also the type information, for example `Ingredient[String]("order-id")` creates an ingredient of name "order-id"
of type "String", for more information about Baker types please refer to [this section](../../reference/baker-types-and-values/).
As shown in the code, events might carry ingredients, and have a maximum about of times they are allowed to fire, the 
runtime will enforce this limit. For more information about this and other features of events please refer to [this section](../../reference/dsls/#events).

## Interactions

Then, the desired actions can be modeled as `interactions`, in our case we are told that it exists a warehouse service 
which we need to call to reserve the items, but this might either succeed or fail.

_Note: Notice that when using the reflection API, the Java interface or Scala trait that will represent your interaction
must have a method named `apply`, this is the method that the reflection API will convert into Baker types/ingredients/events._

```scala tab="Scala"

object Interactions {
    
    val ReserveItems: Interaction = Interaction(
          name = "ReserveItems",
          inputIngredients = Seq(
            Ingredients.OrderId,
            Ingredients.Items,
          ),
          output = Seq(
            Events.OrderHadMissingItems,
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

```scala tab="Java (Reflection API)"

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
        ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("items") List<String> items);
    }
    
}

```

An interaction resembles a function, it takes input ingredients and outputs 1 of several possible events. At runtime, when
an event fires, baker tries to match the provided ingredients of 1 or several events to the input of awaiting interactions,
as soon as there is a match on data, baker will execute the interactions, creating a cascading effect that will execute
your business process in an asynchronous manner.

This was a simple example, but you might have already concluded that this can be further composed into bigger processes by
making new interactions that require events and ingredients which are output of previous interactions. 

You can create also interactions which take no input ingredients but are executed after events (with or without provided 
ingredients) are fired, for this and other features please refer to the conceptual documentation found [here](../../reference/dsls/#events).

## The Recipe

The final step is to create an object that will hold all of these descriptions into what we call a Recipe, this becomes
the "blueprint" of your process, it can define failure handling strategies, and will "auto-bind" the interactions, that 
means it detects the composition between interactions by matching the ingredients provided by events to the input ingredients
required by interactions.

```scala tab="Scala"

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

```scala tab="Java"

public class JWebshopRecipe {

    // ... previous events and interactions.

    public final static Recipe recipe = new Recipe("WebshopRecipe")
            .withSensoryEvents(OrderPlaced.class)
            .withInteractions(of(ReserveItems.class));
}
```

Let us remember that this is just a _description_ of what our program across multiple services should do, on the next 
sections we will see how to visualize it, create runtime `instances` of our recipes and their parts, what common practices
are there for testing, everything you need to know to deploy and monitor a baker cluster, and how Baker helps you handle
and resolve failure which is not modeled in the domain (in the recipe).

As you might have realised `Ingredients`, `Events` and `Interactions` could be reused on different Recipes, giving common
business verbs that your programs and organisation can use across teams, the same way different cooking recipes share
same processes (simmering, boiling, cutting) you should reuse interactions across your different business recipes.

As a bonus; you might have though that this API is verbose, we agree and that is why we developed an alternative 
API which uses Java and Scala reflection.

``` scala tab="Scala (Reflection API)"

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

``` scala tab="Java (Reflection API)"

package webshop;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.Recipe;

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

        // The @FireEvent annotation communicates the reflection API about several possible outcome events.
        @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
        // The @RequiresIngredient annotation communicates the reflection API about the ingredient names that other events
        // must provide to execute this interaction.
        ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("items") List<String> items);
    }

    public final static Recipe recipe = new Recipe("WebshopRecipe")
            .withSensoryEvents(OrderPlaced.class)
            .withInteractions(of(ReserveItems.class));
}
```
