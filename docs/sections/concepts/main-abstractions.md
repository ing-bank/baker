# Main Abstractions

Baker makes a strong division between the specification of your business process and the runtime implementations.

| Specification | Runtime |
|---------------|---------|
| Type | Value |
| Ingredient | IngredientInstance |
| Event | EventInstance |
| Interaction | InteractionInstance |
| Recipe | RecipeInstance |

The first 4 are used to create `Recipes` which serve as "blueprints" of your process. And in the Baker
runtime they are used in the `RecipeInstances`, which are created from a `Recipe` specification.

## Type and Values

Because of the distributed nature of Baker and how the runtime works, we need to have serializable types to 
transfer recipes between nodes and to match over data, that is why we implemented a type system on top of Scala.
They help not just to model your domain but also for Baker to identify when to execute interactions as soon as
the data is available.

Examples of types and values in baker:

``` scala tab="Scala"
import com.ing.baker.types._

val data: (Type, Value) = (Int32, PrimitiveValue(42))
```

``` java tab="Java"
```

Full documentation about the type system can be found [here]().

## Ingredient

Ingredients are _pure data_, This data is **immutable**, which means that it can only be created and never 
mutated through the process. And there is **no subtyping** or hierarchy.

## Event

## Interaction

## Recipe