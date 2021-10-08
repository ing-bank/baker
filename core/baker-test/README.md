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
      - [isEqual](#isequal)
      - [isNull](#isnull)
      - [isAbsent](#isabsent)
      - [Custom Ingredient Assert](#custom-ingredient-assert)
    - [Logging](#Logging)
    - [Async](#Async)
    - [Chaining](#Chaining)

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

**java/scala:**
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

#### isEqual

You can assert if an ingredient is equal to expected value:

**java/scala:**
```java
    recipeAssert
        .assertIngredient("ingredientName")
        .isEqual(ingredientValue);
```

#### isNull

You can assert if an ingredient is null (existing ingredient but is equal null):

**java:**
```java
    recipeAssert
        .assertIngredient("direction")
        .isNull();
```
**scala:**
```scala
    recipeAssert
        .assertIngredient("direction")
        .isNull
```

#### isAbsent

You can assert if an ingredient is not part of the recipe:

**java:**
```java
    recipeAssert
        .assertIngredient("not-existing")
        .isAbsent();
```
**scala:**
```scala
    recipeAssert
        .assertIngredient("not-existing")
        .isAbsent
```

#### Custom Ingredient Assert

There is also a possibility to inject custom assert:

**java:**
```java
    recipeAssert
        .assertIngredient("someListOfStrings")
        .is(val -> Assert.assertEquals(2, val.asList(String.class).size()));
```
**scala:**
```scala
    recipeAssert
        .assertIngredient("someListOfStrings")
        .is(value => Assertions.assert(value.asList(classOf[String]).size == 2));
```

### Logging

You can log ingredients of the recipe instance (with values):

**java/scala:**
```java
    recipeAssert.logIngredients();
```

You can log event names that where use in this recipe instance:

**java/scala:**
```java
    recipeAssert.logEventNames();
```

You log the visual state of the recipe in [dot language](https://graphviz.org/doc/info/lang.html):

**java/scala:**
```java
    recipeAssert.logVisualState();
```

You can log all the information available using the following method:

**java/scala:**
```java
    recipeAssert.logCurrentState();
```

### Async

Quite a common example is to wait for the baker process to be finished.
Therefore a blocking method was implemented:

**java/scala:**
```java
    recipeAssert.waitFor(happyFlow);
```

By default the timeout is 10 seconds. You can configure it during `RecipeAssert` construction:

**java:**
```java
    RecipeAssert.of(baker, recipeInstanceId, Duration.ofSeconds(20));
```

**scala:**
```scala
    RecipeAssert(baker, recipeInstanceId, 20 seconds)
```

### Chaining

`RecipeAssert` is chainable:

**java:**
```java
    RecipeAssert.of(baker, recipeInstanceId)
        .waitFor(happyFlow)
        .assertEventsFlow(happyFlow)
        .assertIngredient("ingredientA").isEqual(ingredientValueA)
        .assertIngredient("ingredientB").isEqual(ingredientValueB);
```

**scala:**
```scala
    RecipeAssert(baker, recipeInstanceId)
        .waitFor(happyFlow)
        .assertEventsFlow(happyFlow)
        .assertIngredient("ingredientA").isEqual(ingredientValueA)
        .assertIngredient("ingredientB").isEqual(ingredientValueB)
```