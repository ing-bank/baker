# Runtime

With the [Recipe DSL](recipe-dsl.md) you can create a *description* of your recipe.

This does **not** yet constitute a runnable process. It is just a description.

To execute & manage your recipes you require the *Baker Runtime*.

## Starting the baker runtime
Creating a baker runtime is as easy as calling the empty constructor.
``` java
// Create a Baker Runtime
JBaker baker = new JBaker();
```

Baker is build on top op [akka](https://www.akka.io).

It requires an `ActorSystem` to start. In the previous example the actor system is not provided. In that case baker will create an actor system for you.

If you already have an actor system then you can give it to Baker.

``` java
ActorSystem actorSystem = ActorSystem.create();

JBaker baker = new JBaker(actorSystem);
```

## Adding interaction implementations

Before you can add a recipe all the interactions for that recipe *MUST* have an implemention in Baker.

You can add it like this:

``` java

ValidateOrderImpl validateOrderImpl = new ValidateOrderImpl();

baker.addImplementation(validateOrderImpl);
```

## Compiling your Recipe

Because a recipe is writen in a `DSL` and you have multiple options like `Java` and `Scala`. We need to compile our DSL Recipe to something that Baker understands and can execture.
For this we have a `RecipeCompiler`.

```java
CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
```

!!! hint "Did you know?!"
    You can use a compiled recipe to create a visual representation. [See the visualization page how to create a visual graph.](recipe-visualization.md)


## Adding your Compiled Recipe

You will need tell baker which Compiled Recipe to run. Giving the Compiled Recipe will give you recipeId. Which you will need to create process instances.

```java
String recipeId = baker.addRecipe(compiledRecipe);
```

## Putting it all together

Combining all these steps with give us the following:

```java
// Implementations, probably defined in other files
ValidateOrderImpl validateOrderImpl = new ValidateOrderImpl();
ManufactureGoodsImpl manufactureGoodsImpl = new ManufactureGoodsImpl();

// Compiling the Recipe
CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);

// Creating a Baker Runtime
JBaker baker = new JBaker();

// Add the Implementations
baker.addImplementations(validateOrderImpl, manufactureGoodsImpl);

// Add the Compiled Recipe
String recipeId = baker.addRecipe(compiledRecipe);
```

Baker is now ready to create an instance for the recipe and execute it.