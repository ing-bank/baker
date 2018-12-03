# Event Listener

Often it may be of interest to be notified of *events* that occur while operating Baker.

There are 2 types of events that can be subscribed to.

1. [Events](concepts.md#event) defined in your recipe that occur in the context of a process instance.
2. Technical / internal events that occur within the baker runtime.

### Important limitations

1. Event delivery is *asynchronous*, **NO** order guarantee is given

    All events *do* come with time stamps.

2. Event delivery is **AT MOST ONCE**

    In case of ungraceful shutdown, you may miss events.

Because of these limitations it is **not** recommended to use these listeners for primary business logic.

## Process instance events

You might be interested which [Events](concepts.md#event) are raised for process instances of a recipe.

For this purpose there is an [EventListener](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/EventListener.scala) interface.

You may implement this interface and register it to Baker.

``` scala tab="Scala"
val listener: EventListener = new EventListener {
   override def processEvent(processId: String, event: RuntimeEvent) = ???
}

val baker: Baker = ??? // initialize baker

baker.registerEventListener(listener);
```

``` java tab="Java"
EventListener listener = new EventListener() {
   @Override
   public void processEvent(String processId, RuntimeEvent event) {
      //
   }
}

JBaker baker = null; // initialize baker

baker.registerEventListener(listener);

```


## Internal events

For the purpose of logging, tracing, etc.. is is possible to register to *internal* events that happen inside Baker.


### List of events

| Class | Description |
| ---   | --- |
| [ProcessCreated](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/ProcessCreated.scala) | A process instance was created |
| [EventReceived](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/EventReceived.scala) | A sensory event for a process instance was received |
| [EventRejected](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/EventRejected.scala) | A sensory event for a process instance was rejected |
| [InteractionStarted](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionStarted.scala) | An interaction started executing |
| [InteractionCompleted](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionCompleted.scala) | An interaction completed executing |
| [InteractionFailed](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionFailed.scala) | An interaction failed during execution |
| [RecipeAdded](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/RecipeAdded.scala) | A Recipe was added |


### Subscription mechanism

You can subscribe to these events by registering a listener to baker.

In scala [partial functions](https://www.scala-lang.org/api/2.12.1/scala/PartialFunction.html) are used.

In java you can register objects that have methods annotated with `@Subscribe`.

In case you are interested in *ALL* events you can register to the general [BakerEvent](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/BakerEvent.scala).

In the example below a listener is registered that is only interested in `EventReceived`:

``` scala tab="Scala"
import com.ing.baker.runtime.core.events._

val baker: com.ing.baker.runtime.core.Baker = ??? // initialize baker

baker.registerListenerPF {

    case e: EventReceived => // ...
}
```

``` java tab="Java"

import com.ing.baker.runtime.core.events.*;

class Subscriber {

   @Subscribe
   public void receiveEventReceived(EventReceived event) {
      // ...
   }
}

com.ing.baker.runtime.java_api.JBaker baker = null; // initialize baker

baker.registerEventListener(new Subscriber());

```

