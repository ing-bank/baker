# Design a Recipe

_The full project examples including tests and configuration can be found [here](https://github.com/ing-bank/baker/tree/master/examples)._

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
      name = "Order Placed",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )
}

```

``` java tab="Java"
```

Depending on your programming language, you might want to import the corresponding dsl, i.e. `scaladsl` vs `javadsl`.

Ingredients and events are just data structures that describe your process data, carrying not just the names, but
also the type information, for example `Ingredient[String]("order-id")` creates an ingredient of name "order-id"
of type "String", for more information about Baker types please refer to [this section](). As shown in the code, events might carry
ingredients, and have a maximum about of times they are allowed to fire, the runtime will enforce this limit. For more 
information about this and other features of events please refer to [this section]().

Then, the desired actions can be modeled as `interactions`, in our case we are told that it exists a warehouse service 
which we need to call to reserve the items, but this might either succeed or fail.

```scala tab="Scala"

object Interactions {
    
    val ReserveItems: Interaction = Interaction(
          name = "Reserve Items",
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
      name = "Order Had Unavailable Items",
      providedIngredients = Seq(
        Ingredients.UnavailableItems
      ),
      maxFiringLimit = Some(1)
    )

    val ItemsReserved: Event = Event(
      name = "Items Reserved",
      providedIngredients = Seq(
        Ingredients.ReservedItems
      ),
      maxFiringLimit = Some(1)
    )
}

```

```scala tab="Java"

```

An interaction resembles a function, it takes input ingredients and outputs 1 of several possible events. At runtime, when
an event fires, baker tries to match the provided ingredients of 1 or several events to the input of awaiting interactions,
as soon as there is a match on data, baker will execute the interactions, creating a cascading effect that will execute
your business process in an asynchronous manner.

This was a simple example, but you might have already concluded that this can be further composed into bigger processes by
making new interactions that require events and ingredients which are output of previous interactions. 

You can create also interactions which take no input ingredients but are executed after events (with or without provided 
ingredients) are fired, for this and other features please refer to the conceptual documentation found [here]().

The final step is to create an object that will hold all of these descriptions into what we call a Recipe.


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
```

Let us remember that this is just a _description_ of what our program across multiple services should do, on the next 
sections we will see how to visualize it, create runtime `instances` of our recipes and their parts, what common practices
are there for testing, everything you need to know to deploy and monitor a baker cluster, and how Baker helps you handle
and resolve failure which is not modeled in the domain (in the recipe).

As a bonus; you might have though that this API is verbose, we agreed as well so we developed an alternative 
API which uses Java and Scala reflection.

``` scala tab="Scala (Reflection API)"

case class OrderPlaced(orderId: String, items: List[String])

sealed trait ReserveItemsOutput

case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

trait ReserveItems {

    @AsyncInteraction
    @FiresEvent(oneOf = Array(classOf[OrderHadUnavailableItems], classOf[ItemsReserved]))
    def apply(@Named recipeInstanceId: String, @Named orderId: String, @Named items: List[String]): Future[ReserveItemsOutput]
}

val recipe: Recipe = Recipe("Webshop")
.withSensoryEvents(
  Event[OrderPlaced],
  Event[OrderHadUnavailableItems],
  Event[ItemsReserved]
)
.withInteractions(
  Interaction[ReserveItems]
)
```

``` scala tab="Java (Reflection API)"
```
