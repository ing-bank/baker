# Migration Guide v3

## From 2.X.X to 3.0.0

This guide only describes how to migrate your existing application.
For a full list new features see the [release notes](../baker-3-release-notes).

Summary:

- *ALL* persisted data from older baker versions *IS COMPATIBLE* and can be used with `3.0.0`
- When running a cluster *DOWNTIME IS REQUIRED* because of binary incompatible changes in the message protocol.
- Code changes are needed to comply to the new Baker interface
- No code changes needed to the Recipe (except the removal of the sieve concept)

### Downtime required for clusters with state

In `3.0.0` some binary incompatible changes where made in the message protocol.

This requires you to bring down the entire cluster (`2.x.x`) and bring it up again (`3.0.0`).

A rolling deploy is tested but is NOT recommended.
During the rolling deploy messages regarding handling events will fail.
It is safer to bring the complete cluster down.

### Renames/package changes

* com.ing.baker.runtime.core -> com.ing.baker.runtime.javadsl/scaladsl/common (depends per object)
* com.ing.baker.runtime.java_api -> com.ing.baker.runtime.javadsl
* processId -> recipeInstanceId
* getProcessId -> GetRecipeInstanceId
* RuntimeEvent -> EventInstance
* ProcessState -> RecipeInstanceState


### Future and CompletableFuture
The new Java and Scala interfaces now almost always return a Future or CompletableFuture.
It is now up to the user to handle waiting for the completion of this future.
This can either be by blocking directly or by 'correctly' programming with these Futures.
We REALLY advise to invest in programming in a non blocking fashion!

```scala tab="Scala"
//Blocking
val futureStatus: Future[SensoryEventStatus] = baker.fireEventAndResolveWhenReceived(orderId, event)
val status: SensoryEventStatus = Await.result(futureStatus, 10 seconds)

//Non Blocking
val futureStatus: Future[SensoryEventStatus] = baker.fireEventAndResolveWhenReceived(orderId, event)
futureStatus.map(sensoryEventStatus => {
     //Code to handle status
})
```

```java tab="Java"
//Blocking
CompletableFuture<SensoryEventStatus> futureStatus =
                baker.fireEventAndResolveWhenReceived(uuid.toString(), EventInstance.from(new ExampleEvent()));
SensoryEventStatus sensoryEventStatus = futureStatus.get();


//Non blocking
CompletableFuture<SensoryEventStatus> futureStatus =
                baker.fireEventAndResolveWhenReceived(uuid.toString(), eventInstance));

futureStatus.thenApply(sensoryEventStatus -> {
      //Code to handle status
});
```

Any Exceptions that used to be thrown by Baker are now encapsulated in the Future/CompletableFuture.
For the CompletableFuture the original exception is wrapped in the ExecutionException.
This is how CompletableFuture work and there is no way around it.

```java tab="Java"
//Blocking
try {
    baker.fireEventAndResolveWhenCompleted(processId, EventInstance.from(new ExampleEventClass())).get();
} catch (ExecutionException e) {
    if(e.getCause() instanceof BakerException.NoSuchProcessException) {
        //Code to handle NoSuchProcessException
    }
    //Code to handle other Exceptions
}


//Non blocking
baker.fireEventAndResolveWhenCompleted(processId, EventInstance.from(new ExampleEventClass()))
        .exceptionally(exception -> {
            if(exception.getCause() instanceof BakerException.NoSuchProcessException) {
                //Decide on what to return on NoSuchProcessException
            }
            //Decide on what to return on other Exceptions
        });
```



### Creating a Baker instance
A Baker instance is now created not with a constructor but via a static method.

For Java the JBaker is gone and you now create a Baker under the javadsl package.

```scala tab="Scala"
import com.ing.baker.runtime.scaladsl.*;
......
val actorSystem: ActorSystem = ActorSystem("WebshopSystem")
val materializer: Materializer = ActorMaterializer()
val config: Config = ConfigFactory.load()
val baker = Baker.akka(config, actorSystem);

```

```java tab="Java"
import com.ing.baker.runtime.javadsl.*;
......
ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
Materializer materializer = ActorMaterializer.create(actorSystem);
Config config = ConfigFactory.load();
Baker baker = Baker.akka(config, actorSystem);
```

See the [runtime reference](../../reference/runtime) for more details


### Adding Interactions into Baker
When adding InteractionInstances formerly known as InteractionImplementations to Baker you now need to give a real InteractionInstance object.

```scala tab="Scala"
val reserveItemsInstance: InteractionInstance =
    InteractionInstance.unsafeFrom(new ReserveItemsInstance)
baker.addInteractionInstance(reserveItemsInstance)
```

```java tab="Java"
InteractionInstance reserveItemsInstance =
    InteractionInstance.from(new ReserveItemsInstance());
baker.addInteractionInstance(reserveItemsInstance)
```

### Firing events
The processEvent has been completely rewritten and is now named FireEvent.
See the [release note](../baker-3-release-notes/#firing-events-into-baker) or [fire event section](../../development-life-cycle/bake-fire-events-and-inquiry/#fire-events) for more details

### Small changes
* dropped .withSieves on the recipe, add these with .withInteractionInstances
* removed support in the interface for UUID, for interaction interfaces a UUID is still supported for backwards compatability reasons.

### About Artery for Akka remoting
Akka has released a new remoting protocol called [Artery](https://doc.akka.io/docs/akka/current/remoting-artery.html)
This is very interesting for Baker users that have Akka cluster.
We have successfully migrated to this from the old remoting and see stability and performance gains.

### Dependency
We have noticed that when using Baker in a maven project the dependencies are not always take over correctly.
If you have the following dependencies in your project please upgrade them:
* org.typelevel.cats-core_2.12 1.5.0
* org.typelevel.cats-effect_2.12 1.2.0
* All Akka dependencies to 2.5.22 (should work with other 2.5.X versions but 2.5.22 is the one we tested).