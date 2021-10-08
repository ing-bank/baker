# Baker Test

This library contains tooling to simplify the testing of the baker based logic, 
especially when asynchronous recipe execution is involved. 
The goal was to make it easy to work with both `java` and `scala`.

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

`EventsFlow` is made to simplify the work with the baker events while testing. `EventsFlow` is immutable.

### Create EventsFlow

It is possible to create a new events flow from events classes:

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

Or a new events flow can be created from existing one:

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

It is also possible to combine classes, strings and other events flows:

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

Events flows are compared ignoring the order of the events:

**java:**

```java
   EventsFlow.of("EventOne","EventTwo").equals(EventsFlow.of("EventTwo","EventOne")); // true   
```

**scala:**

```scala
   "EventOne" :: "EventTwo" :: EmptyFlow == "EventTwo" :: "EventOne" :: EmptyFlow // true   
```

While comparing events flows it does not matter if an event is provided as a class or as a string:

**java:**

```java
   EventsFlow.of(EventOne.class).equals(EventsFlow.of("EventOne")); // true   
```

**scala:**

```scala
   classOf[EventOne] :: EmptyFlow == "EventOne" :: EmptyFlow // true   
```

## RecipeAssert

To create a recipe assert instance a baker instance and a recipe instance id are required:

**java:**
```java
    RecipeAssert recipeAssert = RecipeAssert.of(baker, recipeInstanceId);
```

**scala:**
```scala
  val recipeAssert: RecipeAssert = RecipeAssert(baker, recipeInstanceId);
```

### Assert Events Flow

There is a way to assert if the events flow for this recipe instance is exactly the same as expected:

**java/scala:**
```java
    recipeAssert.assertEventsFlow(happyFlow);
```

If it is not the same a clear error message of what is the difference is provided:

```text
Events are not equal:
    actual: OrderPlaced, ItemsReserved
  expected: OrderPlaced, ItemsNotReserved
difference: ++ ItemsNotReserved
            -- ItemsReserved
```

### Assert Ingredients

!!Provides a simple way to assert ingredient values.

#### isEqual

!!Asserts if the ingredient value is equal to the expected value:

**java/scala:**
```java
    recipeAssert
        .assertIngredient("ingredientName")
        .isEqual(ingredientValue);
```

#### isNull

Asserts if the ingredient exists and has `null` value:

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

Asserts if the ingredient is not a part of the recipe:

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

Custom ingredient asserts are also possible:

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

!!Logs ingredients (with values) of the recipe instance:

**java/scala:**
```java
    recipeAssert.logIngredients();
```

!ogs events names fired for the recipe instance:

**java/scala:**
```java
    recipeAssert.logEventNames();
```

!Logs the visual state of the recipe instance in [dot language](https://graphviz.org/doc/info/lang.html):

**java/scala:**
```java
    recipeAssert.logVisualState();
```

Logs all the information available for the recipe instance:

**java/scala:**
```java
    recipeAssert.logCurrentState();
```

The current state is logged when any of the assertions fails. 

### Async

Quite a common task is to wait for a baker process to finish or specific event to fire.
Therefore, the blocking method was implemented:

**java/scala:**
```java
    recipeAssert.waitFor(happyFlow);
    // on this line all the events within happyFlow have happened
    // otherwise timeout occurs and an assertion error is thrown
```

The default timeout is 10 seconds and it can be configured on the `RecipeAssert` construction:

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