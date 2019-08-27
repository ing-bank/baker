# Release Notes v3

The focus of release 3 of Baker is the Baker runtime.

The first goal of this release is to be more clear in what the Baker runtime does.
We try to achieve this by having a clearer and more truthful interface.

The second goal is to simplify the internal logic of the runtime.
This in turn has increased the performance of Baker for both stateful and stateless processes.

## Clearer and more truthful runtime interface


### New approach to Java and Scala DSL for the runtime
In the past the Baker runtime was created for Scala developers and returned Scala objects.
For Java developers we create the JBaker which wrapped around the Baker and translated the objects.
The problem with this approach was that the interfaces for Java and Scala developers was going out of sync.

In this release we have created two separate packages for Java and Scala interfaces.
The javadsl and scaladsl packages contain the same objects but created for those users in mind.
These objects share a common parent to ensure the Java and Scala runtime DSLs are in sync.
The user you now just chooses the correct objects by having either the javadsl or scaladsl imported.

### Future and CompletableFuture
One of the things that Baker was hiding from the user is that is did a lot of blocking operations.
It was also unneeded to block since internally everything already supported using async operations.

In this release we have adjusted almost all interfaces of Baker to return a Future (or CompletableFuture for Java).
This way Baker does not block anymore and the user is in control.
The user can now program with Baker in a more functional way by using these futures.
If you as user do not want to you can wait for the result and its clear that the thread is blocked.

### Renames to runtime objects
One of the things that was unclear is how the runtime objects map to the objects in the Recipe.
To make this clearer we have renamed some of the runtime objects.

They now map in the following fashion

| Specification | Runtime |
|---------------|---------|
| `Type` | `Value` |
| `Ingredient` | `IngredientInstance` |
| `Event` | `EventInstance` |
| `Interaction` | `InteractionInstance` |
| `Recipe` | `RecipeInstance` |

This means the following renames have been done

* Process -> RecipeInstance
* ProcessId -> RecipeInstanceId
* RuntimeEvent -> EventInstance
* InteractionImplementation/Implementation -> InteractionInstance

This also translates to all methods on Baker.
For example:

* addImplementation(s) -> addInteractionInstance(s)

### Firing events into Baker
The processEvent logic has been completely rewritten, it is now been renamed to fireEvent.

### EventInstance
In the old versions you could give any object ot the processEvent method and Baker would transform this to an Event.
This made it sometimes unclear what Baker really accepts as Objects.
Instead now you give a EventInstance to Baker.
This has a helper method to create a EventInstance from any Object.
The difference now is that its clear that Baker uses EventInstances.
Another advantage is that you are now also free to create EventInstances any other way.

```scala tab="Scala"
val orderPlaced = EventInstance
      .unsafeFrom(SimpleWebshopRecipeReflection.OrderPlaced(orderId, items))

val orderPlace2 =
        EventInstance.apply("OrderPlaced", Map("orderId"-> Converters.toValue(orderId), "items" -> Converters.toValue(items)))

```

```java tab="Java"
EventInstance firstOrderPlaced =
                EventInstance.from(new JWebshopRecipe.OrderPlaced(orderId, items));

EventInstance firstOrderPlaced2 =
                EventInstance.apply("OrderPlaced", ImmutableMap.of("orderId", Converters.toValue(orderId), "items", Converters.toValue(items)));
```


#### Decide on what to be notified on when firing the event
Like in the old versions you can ask Baker to notify on specific moments.
This can be when the event is received or when the processing is completed.
New in this release is that you can now specify this when firing the event itself.
The advantage is that Baker can optimize the resources it uses in those cases.
This is done using the fireEventAndResolveWhenReceived and fireEventAndResolveWhenCompleted methods.

```scala tab="Scala"
val result: Future[SensoryEventStatus] = baker.fireEventAndResolveWhenReceived("recipeInstanceId", orderPlaced)
val result: Future[SensoryEventResult] = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade)
```

```java tab="Java"
CompletableFuture<SensoryEventStatus> result = baker.fireEventAndResolveWhenReceived(recipeInstanceId, paymentMade);
CompletableFuture<SensoryEventResult> result = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced);
```

#### Wait for a specific Event
A new moment you can ask Baker to notify you on is on a specific Event.
You can use the fireEventAndResolveOnEvent method for this.

```scala tab="Scala"
val result: Future[SensoryEventResult] = baker.fireEventAndResolveOnEvent("recipeInstanceId", orderPlaced, "eventName")
```

```java tab="Java"
CompletableFuture<SensoryEventResult> result =
                baker.fireEventAndResolveOnEvent("recipeInstanceId", firstOrderPlaced, "eventName");
```

#### EventResult
When firing a event and waiting for completion stage or waiting for a specific event a EventResult object will be returned.
This EventResult object contains the SensoryEventStatus, event names and created ingredients.
This can be useful if you need to make a decision depending on the state.
In these cases there is no need to inquire on Baker itself anymore.

```scala tab="Scala"
case class SensoryEventResult(
                               sensoryEventStatus: SensoryEventStatus,
                               eventNames: Seq[String],
                               ingredients: Map[String, Value]
) extends common.SensoryEventResult with ScalaApi
```

```java tab="Java"
case class SensoryEventResult(
                               sensoryEventStatus: SensoryEventStatus,
                               eventNames: java.util.List[String],
                               ingredients: java.util.Map[String, Value]
) extends common.SensoryEventResult with JavaApi {

  def getSensoryEventStatus: SensoryEventStatus = sensoryEventStatus

  def getEventName: java.util.List[String] = eventNames

  def getIngredients: java.util.Map[String, Value] = ingredients
}
```

See the [fire event section](../../development-life-cycle/bake-fire-events-and-inquiry/#fire-events) for more details.


### New EventListener functions
For the EventListener we have moved away from the annotation based approach.
In this version you can add a EventListener function instead.
See the [event listener section](http://localhost:8000/sections/reference/event-listener/) for more details.

## Improved and simplified Runtime
### Better performance
Due to simplifying and refactoring the runtime we see a big increase in the load Baker can handle.
For our created [example project](https://github.com/ing-bank/baker/tree/master/examples/src)
we saw the project could handle over 5 times the load when switching between version 2 and 3 of Baker.

### New journal for stateless processes
For stateless processes we advised to use the in-memory-journal plugin.
This journal still kept all processes in-memory until the actors where cleaned.
For a true stateless process this is unnecessary so we crated a new journal.
This one just dumps the messages directly without keeping it in memory.
This should lower the memory footprint of stateless users.
TODO add description how to use this.

### Support for Async interactions
TODO describe how to use his

###

## Deprecated/Removed
### EventListener
The EventListener object used in the Java runtime has been deprecated.
We advice users to move over the logic to the registerBakerEventListener that accepts functions instead.

### Sieves
The Sieve concept has slowly been deprecated in the last releases.
In version 2 there was already no difference between a sieve and an interaction.
In this release we have removed sieves completely.

### UUID support
In JBaker we supported using a UUID as a processId.
In this release this has been removed completely and we accept Strings.
This is again in line with being clearer what Baker does.
Internally we where just transforming this to a String.