# Design a Recipe

_The full project examples including tests and configuration can be found [here](https://github.com/ing-bank/baker/tree/master/examples)._

The _Development Life Cycle_ section provides a "top-down"/"by-example" guide to baker, all of the concepts 
are introduced through exemplification on hypothetical development situations.

## Example 1: Order placement process for a Webshop

The recipe DSL allows you to declaratively describe your business process. The design always starts with the
business requirements, lets say you are developing a webshop which will have many different microservices on 
the backend. The initial requirements for the order reservation process reads: 

_"An order contains an order id and a list of store item identifiers, when an order is placed it must first 
be validated by reserving the items from the warehouse service, a success scenario yields the ids of the 
reserved items, but if at least one item is missing, a failure scenario yields the list of unavailable items and the
process stops"_

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
      Ingredient[String]("order-id")

    val Items: Ingredient[List[String]] =
      Ingredient[List[String]]("items")
}

object Events {

    val OrderPlaced: Event = Event(
      name = "order-placed",
      providedIngredients = Seq(
        Ingredients.OrderId,
        Ingredients.Items
      ),
      maxFiringLimit = Some(1)
    )
}
```

``` java tab="Java"
//TODO
```

Depending on your programming language, you might want to import the corresponding dsl, i.e. `scaladsl` vs `javadsl`.

Ingredients and events are just data structures that describe your process data, carrying not just the name, but
also the type information, for example `Ingredient[String]("order-id")` creates an ingredient of name "order-id"
of type "String", for more information about Baker types please refer to [this]().

Then, the desired actions can be modeled as `interactions`, 