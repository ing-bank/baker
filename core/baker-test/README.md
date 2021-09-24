# Baker Test

This repository contains some tools to make it easier to test your baker processes. Our goal was to make it easy to work
using both `java` and `scala`.

This library has the following features:

* [EventsFlow](#EventsFlow)
* [RecipeAssert](#RecipeAssert)
    - [Assert Events](#Assert Events)
    - [Assert Ingredients](#Assert Ingredients)
    - [Logging](#Logging)
    - [Chaining](#Chaining)
    - [Async](#Async)

## EventsFlow

EventsFlow is made to simplify the work with events within Baker while testing. EventFlow is immutable.

### Create EventsFlow

You can create events flows from classes:

**java:**

```java
    EventsFlow flow=EventsFlow.of(
        SomeSensoryEvent.class,
        InteractionSucceeded.class
    );
```

**scala:**

```scala
   val flow: EventsFlow = classOf[SomeSensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow
```

You can create new event flows from other event flows:

**java:**

```java
    EventsFlow anotherFlow=flow
        .remove(SomeSensoryEvent.class)
        .add(AnotherSensoryEvent.class);
```

**scala:**

```scala
    val anotherFlow: EventsFlow = flow -- classOf[SomeSensoryEvent] ++ classOf[AnotherSensoryEvent]
```

### EventsFlow possibilities

You can combine classes, strings and another flows in the event flows:

**java:**

```java
    EventsFlow unhappyFlow=happyFlow
        .remove(InteractionSucceeded.class)
        .add("InteractionExhausted")
        .add(someErrorFlow);
```

**scala:**

```scala
    val unhappyFlow: EventsFlow = happyFlow -- classOf[InteractionSucceeded] ++ "InteractionExhausted" +++ someErrorFlow
``` 

### EventsFlow comparison

You can compare them and the order does not matter:

**java:**

```java
   EventsFlow.of("EventOne","EventTwo").equals(EventsFlow.of("EventTwo","EventOne")); // true   
```

**scala:**

```scala
   "EventOne" :: "EventTwo" :: EmptyFlow == "EventTwo" :: "EventOne" :: EmptyFlow // true   
```

While comparing it does not matter if it is a class or a string:

**java:**

```java
   EventsFlow.of(EventOne.class).equals(EventsFlow.of("EventOne")); // true   
```

**scala:**

```scala
   classOf[EventOne] :: EmptyFlow == "EventOne" :: EmptyFlow; // true   
```

## RecipeAssert

To create baker assert instance you have to provide a baker instance and a process id:

```java
    RecipeAssert recipeAssert=RecipeAssert.of(baker,uuid)
```

### Assert Events

You can assert if event flow for this process id is exactly the same as expected:

```java
    recipeAssert.assertEventsFlow(LEFT);
```

If it is not the same you will get a clear error message of what is the difference:

```text
// FIXME
```

You can also assert flows with classes:

```java
    recipeAssert.assertEventsFlow(FirstEventClass.class,SecondEventClass.class);
```

or with strings:

```java
    recipeAssert.assertEventsFlow("FirstEventClass","SecondEventClass");
```

You can also assert if some event or a set of events happen.

```java
    recipeAssert.assertEventsHappened(FirstEventClass.class,SecondEventClass.class);
```

In this case it does not check for the exact flow but whether the expected events exist in the flow.

The same can be done using strings:

```java
    recipeAssert.assertEventsHappened("FirstEventClass","SecondEventClass");
```

You can also assert if some event or a set of events did not happen:

```java
    recipeAssert.assertEventsNotHappened(FirstEventClass.class,SecondEventClass.class);
```

The same can be done using strings:

```java
    recipeAssert.assertEventsNotHappened("FirstEventClass","SecondEventClass");
```

### Assert Ingredients

You can assert ingredient values.

You can assert if it is equal to expected value:

```java
    recipeAssert.assertIngredient(TestRecipe.TestSensoryEvent.class,"direction").isEqual(TestRecipe.Direction.LEFT);
```

You can assert if it is null:

```java
    recipeAssert.assertIngredient(TestRecipe.TestSensoryEvent.class,"direction").isNull();
```

or if it is not null:

```java
    recipeAssert.assertIngredient(TestRecipe.TestSensoryEvent.class,"direction").notNull();
```

If it is not enough there is a possibility to inject custom check:

```java
    recipeAssert.assertIngredient("someList").customAssert(val->Assert.assertEquals(2,val.asList(String.class).size()));
```

### Logging

You can print events with ingredients:

```java
    recipeAssert.printEvents();
```

or just event names:

```java
    recipeAssert.printEventNames();
```

You can print diagram:

```java
    recipeAssert.printDiagram();
```

### Chaining

RecipeAssert is chainable:

```java
    RecipeAssert.of(baker,uuid)
        .printEvents()
        .printDiagram()
        .assertEventsFlow(LEFT)
        .assertIngredient(TestRecipe.TestSensoryEvent.class,"direction")
        .isEqual(TestRecipe.Direction.LEFT);
```

### Async

Quite a common example is to wait for the baker process to be finished.

// TODO finish 

