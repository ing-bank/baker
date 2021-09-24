# Baker Test

This repository contains some tools to make it easier to test your baker processes. Our goal was to make it easy to work
using both `java` and `scala`.

**java:**

```java
  BakerAssert.of(baker, recipeInstanceId)
        .waitFor(EventsFlow.of(SensoryEvent.class, InteractionSucceeded.class))
        .assertIngredient("testIngredient").isEqual("foo")
```

**scala:**

```scala
  BakerAssert(baker, recipeInstanceId)
        .waitFor(classOf[SensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow)
        .assertIngredient("testIngredient").isEqual("foo")
```

This library has the following features:

* [EventsFlow](#EventsFlow)
* [RecipeAssert](#RecipeAssert)
    - [Assert Events Flow](#assert-events-flow)
    - [Assert Ingredients](#assert-ingredients)
    - [Logging](#Logging)
    - [Chaining](#Chaining)
    - [Async](#Async)

## EventsFlow

EventsFlow is made to simplify the work with events within Baker while testing. EventFlow is immutable.

### Create EventsFlow

You can create events flows from classes:

**java:**

```java
    EventsFlow flow = EventsFlow.of(
        SomeSensoryEvent.class,
        InteractionSucceeded.class
    );
```

**scala:**

```scala
   val flow: EventsFlow = 
      classOf[SomeSensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow
```

You can create new event flows from other event flows:

**java:**

```java
    EventsFlow anotherFlow = flow
        .remove(SomeSensoryEvent.class)
        .add(AnotherSensoryEvent.class);
```

**scala:**

```scala
    val anotherFlow: EventsFlow = 
      flow -- classOf[SomeSensoryEvent] ++ classOf[AnotherSensoryEvent]
```

### EventsFlow possibilities

You can combine classes, strings and another flows in the event flows:

**java:**

```java
    EventsFlow unhappyFlow = happyFlow
        .remove(InteractionSucceeded.class)
        .add("InteractionExhausted")
        .add(someErrorFlow);
```

**scala:**

```scala
    val unhappyFlow: EventsFlow = 
        happyFlow -- classOf[InteractionSucceeded] ++ "InteractionExhausted" +++ someErrorFlow
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
   classOf[EventOne] :: EmptyFlow == "EventOne" :: EmptyFlow // true   
```

## RecipeAssert

To create a recipe assert instance you have to provide a baker instance and a recipe instance id:

**java:**
```java
    RecipeAssert recipeAssert = RecipeAssert.of(baker, recipeInstanceId);
```

**scala:**
```scala
  val recipeAssert: RecipeAssert = RecipeAssert(baker, recipeInstanceId);
```

### Assert Events Flow

You can assert if events flow for this process is exactly the same as expected:

```java
    recipeAssert.assertEventsFlow(happyFlow);
```

If it is not the same you will get a clear error message of what is the difference:

```text
Events are not equal:
    actual: OrderPlaced, ItemsReserved
  expected: OrderPlaced, ItemsNotReserved
difference: ++ ItemsNotReserved
            -- ItemsReserved
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

