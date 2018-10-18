# Runtime

## Starting the baker runtime

Baker is build on top op akka. It requires an `ActorSystem` to start up.

``` java
// if you call baker with a the empty constructor an ActorSystem will be created for you.
JBaker baker = new JBaker();
```

// alternatively you can provide an actor system yourself.
```
ActorSystem actorSystem = ActorSystem.create();

JBaker baker = new JBaker(actorSystem);
```

## Adding interaction implementations

See [here](interactions) how to define and implement an interaction in java. Once you have an implementation you can add it like:

``` java

ValidateOrderImpl validateOrderImpl = new ValidateOrderImpl();

baker.addImplementation(validateOrderImpl);
```

## Adding recipes




## Creating process instances

baker.

## Firing events


``` java

baker.processEvent(processId, new OrderPlaced("order"));

```

##