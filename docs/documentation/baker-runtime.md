# Baker Runtime

With the [Recipe DSL](recipe-dsl.md) you can create a *description* of your recipe.

This does **not** yet constitute a runnable process. It is just a description.

To execute & manage your recipes you require the *Baker Runtime*.

## Starting the baker runtime
Creating a baker runtime is as easy as calling the empty constructor.

``` scala tab="Scala"
// Create a Baker Runtime
val baker = new Baker();
```

``` java tab="Java"
// Create a Baker Runtime
JBaker baker = new JBaker();
```

Baker is build on top op [akka](https://www.akka.io).

It requires an `ActorSystem` to start. In the previous example the actor system is not provided. In that case baker will create an actor system for you.

If you already have an actor system then you can give it to Baker.

``` scala tab="Scala"
val actorSystem = ActorSystem();

Baker baker = new Baker(actorSystem);
```

``` java tab="Java"
ActorSystem actorSystem = ActorSystem.create();

JBaker baker = new JBaker(actorSystem);
```

## Adding interaction implementations

Before you can add a recipe all the interactions for that recipe *MUST* have an implemention in Baker.

You can add them like this:

``` scala tab="Scala"
val validateOrderImpl = new ValidateOrderImpl()

baker.addImplementation(validateOrderImpl)
```

``` java tab="Java"
ValidateOrderImpl validateOrderImpl = new ValidateOrderImpl();

baker.addImplementation(validateOrderImpl);
```

## Compiling your Recipe

A recipe is writen in a `DSL`. This is just a declarative description of your process.

In order to execute it we need to compile it. This connects all the pieces into a graph (more precisly a [petri net](https://en.wikipedia.org/wiki/Petri_net)).

For this purpose there is the `RecipeCompiler`.

``` scala tab="Scala"
val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
```

``` java tab="Java"
CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
```

!!! hint "Did you know?!"
    You can use a compiled recipe to create a visual representation. [See the visualization page how to create a visual graph.](recipe-visualization.md)


## Adding your Compiled Recipe

Once you have compiled your recipe you can add it to Baker.

``` scala tab="Scala"
baker.addRecipe(compiledRecipe)
```

``` java tab="Java"
baker.addRecipe(compiledRecipe);
```

## Putting it all together

Combining all these steps gives us the following:

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