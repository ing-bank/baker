# Events

## Subscribing to internal events

### Considerations

1. Event delivery is *asynchronous*, **NO** order guarantee is given

    All events *do* come with time stamps.

2. Event delivery is **AT MOST ONCE**

    It is not recommended to use for primary business logic

### List of events

| class | description |
| ---   | --- |
| [ProcessCreated](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/ProcessCreated.scala) | A process instance was created |
| [EventReceived](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/EventReceived.scala) | A sensory event for a process instance was received |
| [EventRejected](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/EventRejected.scala) | A sensory event for a process instance was rejected |
| [InteractionStarted](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionStarted.scala) | An interaction started executing |
| [InteractionCompleted](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionStarted.scala) | An interaction completed executing |
| [InteractionFailed](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/InteractionFailed.scala) | An interaction failed during execution |
| [RecipeAdded](https://github.com/ing-bank/baker/blob/master/runtime/src/main/scala/com/ing/baker/runtime/core/events/RecipeAdded.scala) | A Recipe was added |


### Subscription mechanism

You can subscribe to these events by registering a listener to baker.

In scala [partial functions](https://www.scala-lang.org/api/2.12.1/scala/PartialFunction.html) are used.

In java you can register objects that have methods annotated with `@Subscribe`.

For example, registering a listener only interested in `EventReceived`:

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
