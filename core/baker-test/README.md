# Baker Test

This repository contains some tools to simplify the test process of baker based logic. 
Our goal was to make it easy to work using both `java` and `scala`.

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

`EventsFlow` is made to simplify the work with events within Baker while testing. `EventsFlow` is immutable.

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

You can assert if an ingredient is `null` 
(it will assert that the ingredient is an existing ingredient and is equal to `null`):

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

There is also a possibility to inject custom ingredient assert:

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

You can log event names that where used in this recipe instance:

**java/scala:**
```java
    recipeAssert.logEventNames();
```

You can log the visual state of the recipe in [dot language](https://graphviz.org/doc/info/lang.html):

**java/scala:**
```java
    recipeAssert.logVisualState();
```

You can log all the information available for the recipe instance using the following method:

**java/scala:**
```java
    recipeAssert.logCurrentState();
```

The current state is logged when any of the assert is failed. 

### Async

Quite a common example is to wait for the baker process to be finished.
Therefore a blocking method was implemented:

**java/scala:**
```java
    recipeAssert.waitFor(happyFlow);
    // on this line all the events within happyFlow have happened
    // otherwise an assertion error is thrown and the test has failed
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