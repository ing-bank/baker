# Release Notes v3

The theme of release 3 is the Baker runtime.
We have two goals with this release.

The first goal is to be clearer in what the Baker runtime does.
We try to achieve this by having better naming and more truthful interface.

The second goal is to simplify the internal logic of the runtime.
This help when developing baker and has increased the performance of Baker.

## Clearer and more truthful runtime interface
The interface of Baker has had a complete overhaul.
Most changes are described below.
Our documentation also has been improved considerably so please have a look into this if something is unclear.

### New approach to Java and Scala DSL for the runtime
In the past the Baker runtime was created for Scala developers and returned Scala objects.
For Java developers we create the JBaker which wrapped around the Baker and translated the objects.
The problem with this approach was that the interfaces for Java and Scala developers was going out of sync.

In this release we have created two separate packages for Java and Scala interfaces.
The javadsl and scaladsl packages contain the same objects but created for those users in mind.
These objects share a common parent to ensure the Java and Scala runtime DSLs are in sync.
As user you just chooses the correct objects by having either the javadsl or scaladsl imported.

### No more blocking! Future and CompletableFuture
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

* addImplementation -> addInteractionInstance
* getProcessState -> getRecipeInstanceState

### Firing events into Baker
The processEvent logic has been completely rewritten, it is now been renamed to fireEvent.
See the [fire event section](../../development-life-cycle/bake-fire-events-and-inquiry/#fire-events) for more details.

#### EventInstance
In the old versions you could give any object to the processEvent method and Baker would transform this to an Event.
This made it sometimes unclear what Baker really accepts as a input for this method.
In the new version of Baker you give a EventInstance to Baker.
This is the internal object we where creating from the Object in the past.
The EventInstance in turn can be created form an Object.
The difference now is that its clear that Baker uses EventInstances internally.
Another advantage is that you are now also free to create EventInstances any other way.

=== "Scala"

    ```scala 
    //From any Object
    val orderPlaced = EventInstance
          .unsafeFrom(SimpleWebshopRecipeReflection.OrderPlaced(orderId, items))
    //Using constructor
    val orderPlace2 =
            EventInstance.apply("OrderPlaced", Map("orderId"-> Converters.toValue(orderId), "items" -> Converters.toValue(items)))

    ```

=== "Java"

    ```java 
    //From any Object
    EventInstance firstOrderPlaced =
                    EventInstance.from(new JWebshopRecipe.OrderPlaced(orderId, items));
    //Using constructor
    EventInstance firstOrderPlaced2 =
                    EventInstance.apply("OrderPlaced", ImmutableMap.of("orderId", Converters.toValue(orderId), "items", Converters.toValue(items)));
    ```


#### Decide on what to be notified on when firing the event
Like in the old versions you can ask Baker to notify on specific moments.
This can be when the event is received or when the processing is completed.
New in this release is that you can now specify this when firing the event itself.
The advantage is that Baker can optimize the resources it uses in those cases.
This is done using the fireEventAndResolveWhenReceived and fireEventAndResolveWhenCompleted methods.

=== "Scala"

    ```scala 
    val result: Future[SensoryEventStatus] = baker.fireEventAndResolveWhenReceived(recipeInstanceId, orderPlaced)
    val result: Future[SensoryEventResult] = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade)
    ```

=== "Java"

    ```java 
    CompletableFuture<SensoryEventStatus> result = baker.fireEventAndResolveWhenReceived(recipeInstanceId, paymentMade);
    CompletableFuture<SensoryEventResult> result = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced);
    ```

The old way of firing a event where you get both the co

#### Wait for a specific Event
In this new release we have added a highly requested feature.
YOu can now ask baker to notify you on a a specific event.
You can use the fireEventAndResolveOnEvent method for this.

The returned future will complete when a event with the given name is fired.

=== "Scala"

    ```scala 
    val result: Future[SensoryEventResult] = baker.fireEventAndResolveOnEvent(recipeInstanceId, orderPlaced, "eventName")
    ```

=== "Java"

    ```java 
    CompletableFuture<SensoryEventResult> result =
                    baker.fireEventAndResolveOnEvent(recipeInstanceId, firstOrderPlaced, "eventName");
    ```

#### EventResult
The fireEventAndResolveOnEvent and fireEventAndResolveWhenCompleted return an EventResult.
This EventResult object contains the SensoryEventStatus, event names and created ingredients.
The addition of the event names and ingredients can be very useful if you need to make a decision depending on the state.
In these cases there is no need to inquire on Baker itself anymore.

=== "Scala"

    ```scala 
    case class SensoryEventResult(
                                   sensoryEventStatus: SensoryEventStatus,
                                   eventNames: Seq[String],
                                   ingredients: Map[String, Value]
    ) extends com.ing.baker.runtime.common.SensoryEventResult with ScalaApi
    ```

=== "Java"

    ```java 
    case class SensoryEventResult(
                                   sensoryEventStatus: SensoryEventStatus,
                                   eventNames: java.util.List[String],
                                   ingredients: java.util.Map[String, Value]
    ) extends com.ing.baker.runtime.common.SensoryEventResult with JavaApi {

      def getSensoryEventStatus: SensoryEventStatus = sensoryEventStatus

      def getEventName: java.util.List[String] = eventNames

      def getIngredients: java.util.Map[String, Value] = ingredients
    }
    ```

### New EventListener functions
For the EventListener we have moved away from the annotation based approach.
In this version you can add an EventListener function instead.
See the [event listener section](../../reference/event-listener/) for more details.

## Improved and simplified Runtime
### Better performance
Due to simplifying and refactoring the runtime we see a big increase in the load a Baker instance can handle.
For our created [example project](https://github.com/ing-bank/baker/tree/master/examples/src)
we saw the project could handle over 5 times the load when switching from version 2 to 3 of Baker.

### New journal for stateless processes
For stateless processes we used to advise to use the in-memory-journal plugin.
This journal kept all processes in-memory until the actors where cleaned.
For a true stateless process this is unnecessary so we created a new journal.
This one just dumps the event sourcing messages.
This should lower the memory footprint of stateless users.

How to configure:
```
CONFIG
# Custom journal plugin
service.sink-journal {
  # Class name of the plugin.
  class = "com.ing.baker.runtime.akka.journal.SinkJournalWriter"
  # Dispatcher for the plugin actor.
  plugin-dispatcher = "akka.actor.default-dispatcher"
}

service.sink-snapshot-store {
  # Class name of the plugin.
  class = "com.ing.baker.runtime.akka.journal.SinkSnapshotStore"
  # Dispatcher for the plugin actor.
  plugin-dispatcher = "akka.persistence.dispatchers.default-plugin-dispatcher"
}
akka.persistence {
  journal.plugin = "service.sink-journal"
  snapshot-store.plugin = "service.sink-snapshot-store"
}
```

### Support for async interactions
It is now possible to create interactions that return their events in a Future or CompletableFuture.
When using this Baker can close threads instead of blocking a thread.
Which in turn again improves performance.
The downside of using async interaction is that some validations cannot be done anymore due to type erasure.

To use this in Scala you just return a Future of the result of your interaction.
In Java you need to return a CompletableFuture of your result and add an AsyncInteraction annotation on top of your InteractionInstance.

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
Internally we were just transforming this to a String.

### Accesss to RuntimeEvents
Version 2 would provided undocumented public interfaces returning RuntimeEvent instances.
In version 3, the possibility to get Ingredients provided by a specific Event is gone.
Users should not care where ingredients are provided from.
This could be from an SensoryEvent or as output of a Event from an Interaction.
This should not matter, only if the ingredient is available should matter.
This allow users to flexibly recipes without impacting client code.
