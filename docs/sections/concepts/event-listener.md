# Event Listener

## baker.registerEventListener(recipeName, listenerFunction)

Registers a listener to all runtime events for on a baker instance.

Note that:
- The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
- The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.

Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
- logging
- metrics
- unit tests

```scala tab="Scala"
baker.registerEventListener((recipeInstanceId: String, event: EventInstance) => {
  println(s"Recipe instance : $recipeInstanceId processed event ${event.name}")
})
```

```java tab="Java"
BiConsumer<String, EventInstance> handler = (String recipeInstanceId, EventInstance event) ->
    System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event.name());
    
baker.registerEventListener(handler);
```

## baker.registerBakerEventListener(listenerFunction)

Registers a listener to all runtime BAKER events, these are events that notify what Baker is doing, like `RecipeInstances`
received `EventInstances` or `CompiledRecipes` being added to baker.

Note that:

* The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
* The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.

Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:

* logging
* metrics
* unit tests

```scala tab="Scala"
import com.ing.baker.runtime.scaladsl._

baker.registerBakerEventListener((event: BakerEvent) => {
  event match {
    case e: EventReceived => println(e)
    case e: EventRejected => println(e)
    case e: InteractionFailed => println(e)
    case e: InteractionStarted => println(e)
    case e: InteractionCompleted => println(e)
    case e: ProcessCreated => println(e)
    case e: RecipeAdded => println(e)
  }
})
```

```java tab="Java"
import com.ing.baker.runtime.javadsl.BakerEvent;

baker.registerBakerEventListener((BakerEvent event) -> System.out.println(event));
```

