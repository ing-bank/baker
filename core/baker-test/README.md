# Baker Test

This repository contains some tools to make it easier to test your baker processes.

* [EventsFlow](#EventsFlow)
* [BakerAssert](#BakerAssert)
    - [Assert Events](#Assert Events)
    - [Assert Ingredients](#Assert Ingredients)
    - [Logging](#Logging)
    - [Chaining](#Chaining)
    - [Async](#Async)

## EventsFlow

EventsFlow is made to simplify the work with events within Baker while testing.

You can create events flows from classes:

```java
    EventsFlow LEFT = EventsFlow.of(
            TestRecipe.TestSensoryEvent.class,
            TestRecipe.LeftEvent.class,
            TestRecipe.LeftInteractionSucceeded.class
    );
``` 

You can create a new event flows from other event flows:

```java
    EventsFlow RIGHT = LEFT
            .remove(TestRecipe.LeftEvent.class, TestRecipe.LeftInteractionSucceeded.class)
            .add(TestRecipe.RightEvent.class, TestRecipe.RightInteractionSucceeded.class);
```

You can combine classes and strings in the event flows:

```java
    EventsFlow UNHAPPY_FLOW = LEFT
               .remove(TestRecipe.LeftInteractionSucceeded.class)
               .add("LeftInteractionExhausted");
``` 

You can compare them and the order does not matter:

```java
   BakerEventsFlow.of("EventOne", "EventTwo").equals(BakerEventsFlow.of("EventTwo", "EventOne")); // true   
```

While comparing it does not matter if it is a class or a string:

```java
   BakerEventsFlow.of(EventOne.class).equals(BakerEventsFlow.of("EventOne")); // true   
```

## BakerAssert

To create baker assert instance you have to provide a baker instance and a process id:

```java
    BakerAssert bakerAssert = BakerAssert.of(baker, uuid)
```

### Assert Events

You can assert if event flow for this process id is exactly the same as expected:

```java
    bakerAssert.assertEventsFlow(LEFT);
```

If it is not the same you will get a clear error message of what is the difference:

```text
// FIXME
```

You can also assert flows with classes:

```java
    bakerAssert.assertEventsFlow(FirstEventClass.class, SecondEventClass.class);
```

or with strings:

```java
    bakerAssert.assertEventsFlow("FirstEventClass", "SecondEventClass");
```

You can also assert if some event or a set of events happen.

```java
    bakerAssert.assertEventsHappened(FirstEventClass.class, SecondEventClass.class);
```

In this case it does not check for the exact flow but whether the expected events exist in the flow.

The same can be done using strings:

```java
    bakerAssert.assertEventsHappened("FirstEventClass", "SecondEventClass");
```

You can also assert if some event or a set of events did not happen:

```java
    bakerAssert.assertEventsNotHappened(FirstEventClass.class, SecondEventClass.class);
```

The same can be done using strings:

```java
    bakerAssert.assertEventsNotHappened("FirstEventClass", "SecondEventClass");
```

### Assert Ingredients

You can assert ingredient values.

You can assert if it is equal to expected value:

```java
    bakerAssert.assertIngredient(TestRecipe.TestSensoryEvent.class, "direction").isEqual(TestRecipe.Direction.LEFT);
```

You can assert if it is null:

```java
    bakerAssert.assertIngredient(TestRecipe.TestSensoryEvent.class, "direction").isNull();
```

or if it is not null:

```java
    bakerAssert.assertIngredient(TestRecipe.TestSensoryEvent.class, "direction").notNull();
```

If it is not enough there is a possibility to inject custom check:

```java
    bakerAssert.assertIngredient("someList").customAssert(val -> Assert.assertEquals(2, val.asList(String.class).size()));
```

### Logging

You can print events with ingredients:

```java
    bakerAssert.printEvents();
```

or just event names:

```java
    bakerAssert.printEventNames();
```

You can print diagram:

```java
    bakerAssert.printDiagram();
```

### Chaining

BakerAssert is chainable:

```java
    BakerAssert.of(baker, uuid)
            .printEvents()
            .printDiagram()
            .assertEventsFlow(LEFT)
            .assertIngredient(TestRecipe.TestSensoryEvent.class, "direction")
                .isEqual(TestRecipe.Direction.LEFT);
```

### Async

Quite a common example is to wait for the baker process to be finished.

// TODO finish 

