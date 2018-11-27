# Runtime

In the [DSL](../recipe_dsl) we have defined a *description* of your recipe.

This does **not** yet constitutate a runnable process. It is just a blue print.

To execute & manage your recipes you require the *Baker Runtime*.

## Starting the baker runtime
Creating a baker runtime is as easy as calling the empty constructor.
``` java
// Create a Baker Runtime
JBaker baker = new JBaker();
```

Baker is build on top op [akka](https://www.akka.io).

It requires an `ActorSystem` to start up. In the previous example the actor system is not provided. In that case baker will create an actor system for you.

If you already have an actor system then you can give it to Baker.

``` java
Config config =

ActorSystem actorSystem = ActorSystem.create();

JBaker baker = new JBaker(actorSystem);
```

## Adding Recipe

When

``` java
Config config =

ActorSystem actorSystem = ActorSystem.create();

JBaker baker = new JBaker(actorSystem);
```

When you create a [recipe](../recipe_dsl) in the `DSL` you specify, among others, the interactions.

A recipe on its own does not executute. We need to create a "runable instance" of the recipe.

Which we blabla "Bake the recipe". There we have to specify the real implementations of our recipe.

## Adding interaction implementations

See [here](../interactions) how to define and implement an interaction in java. Once you have an implementation you can add it like:

``` java

ValidateOrderImpl validateOrderImpl = new ValidateOrderImpl();

baker.addImplementation(validateOrderImpl);
```

## Creating a recipe instance


## Firing events


``` java

baker.processEvent(processId, new OrderPlaced("order"));

```

##