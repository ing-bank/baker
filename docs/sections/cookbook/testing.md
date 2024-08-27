# Testing

In general, Baker applications are easy to test because the Baker model enforces separation and decoupling between parts
of
your system. It provides a clear distinction between business logic (the recipe) and implementation details
(interaction implementations). Furthermore, interactions are independent of each other, since every interaction only
depends on its inputs.

This section describes testing strategies for the different layers of a Baker application. And demonstrates how to
simplify testing by using the `baker-test` library.

## Recipe validation tests

A recipe is validated when it's compiled by the `RecipeCompiler`. Any validation errors that might occur during this
compilation are available through the resulting `CompiledRecipe` instance. A simple unit test that checks for
validation errors in your recipe is essential.

=== "Java"

    ```java
    --8<-- "docs-code-snippets/src/test/java/examples/java/recipes/WebShopRecipeTest.java"
    ```

=== "Kotlin"

    ```kotlin
    --8<-- "docs-code-snippets/src/test/kotlin/examples/kotlin/recipes/WebShopRecipeTest.kt"
    ```

=== "Scala"

    ```scala
    --8<-- "docs-code-snippets/src/test/scala/examples/scala/recipes/WebShopRecipeTest.scala"
    ```

## Business logic tests

The next layer is to test that the recipe actually does what you expect it to do at the business logic level. You can
achieve this providing dummy or mock interactions that behave in an expected manner. The objective here is to test that
the Recipe ends on the expected state given a certain order of firing sensory events.

The full test flow looks like this:

1. Setup dummy or mock interactions that behave according to the test scenario.
2. Create a new in memory Baker with the interactions from step 1.
3. Add and bake the recipe
4. Fire sensory events
5. Assert expectations by [querying the state of the recipe](../fire-sensory-events/#inquiry).

## Implementation tests

The final layer is to individually test your implementations, which will resemble your normal e2e tests,
interconnectivity tests, or unit tests. What these tests look like will strongly depend on your teams testing and
coding conventions.

## Baker test library
The `baker-test` library simplifies the testing of baker-based logic. Using this library makes the test code 
concise and readable in both Java and Scala. It also simplifies the testing of the cases when asynchronous recipe 
execution is involved.

!!! Warning
    At the moment `baker-test` is not compatible with the suspending Kotlin Baker APIs.

### Adding the dependency

=== "Maven"

    ```xml 
    <dependency>
      <groupId>com.ing.baker</groupId>
      <artifactId>baker-test_2.13</artifactId>
      <version>${baker.version}</version>
      <scope>test</scope>
    </dependency>
    ```

=== "Sbt"

    ```scala 
    libraryDependencies += "com.ing.baker" %% "baker-test_2.13" % bakerVersion
    ```

### EventsFlow

`EventsFlow` is made to simplify the work with the baker events while testing. `EventsFlow` is immutable.

You create a new events flow from events classes:

=== "Scala"

    ```scala
    val flow: EventsFlow = 
          classOf[SomeSensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow
    ```

=== "Java"

    ```java
    EventsFlow flow = EventsFlow.of(
        SomeSensoryEvent.class,
        InteractionSucceeded.class
    );
    ```

There is also an option to create a new event flow from the existing one:

=== "Scala"

    ```scala
    val anotherFlow: EventsFlow = 
        flow -- classOf[SomeSensoryEvent] ++ classOf[AnotherSensoryEvent]
    ```

=== "Java"

    ```java
    EventsFlow anotherFlow = flow
        .remove(SomeSensoryEvent.class)
        .add(AnotherSensoryEvent.class);
    ```

It is also possible to combine classes, strings and other events flows:

=== "Scala"

    ```scala
        val unhappyFlow: EventsFlow = 
            happyFlow -- classOf[InteractionSucceeded] ++ "InteractionExhausted" +++ someErrorFlow
    ``` 

=== "Java"

    ```java
        EventsFlow unhappyFlow = happyFlow
            .remove(InteractionSucceeded.class)
            .add("InteractionExhausted")
            .add(someErrorFlow);
    ```

Events flows are compared ignoring the order of the events:

=== "Scala"

    ```scala
       "EventOne" :: "EventTwo" :: EmptyFlow == "EventTwo" :: "EventOne" :: EmptyFlow // true   
    ```

=== "Java"

    ```java
       EventsFlow.of("EventOne","EventTwo").equals(EventsFlow.of("EventTwo","EventOne")); // true   
    ```

While comparing events flows it does not matter if an event is provided as a class or as a string:

=== "Scala"

    ```scala
       classOf[EventOne] :: EmptyFlow == "EventOne" :: EmptyFlow // true   
    ```

=== "Java"

    ```java
       EventsFlow.of(EventOne.class).equals(EventsFlow.of("EventOne")); // true   
    ```

### RecipeAssert

`RecipeAssert` is the starting point of all your assertions for the recipe instance.

To create a `RecipeAssert` instance a baker instance and a recipe instance id are required:

=== "Scala"

    ```scala
      val recipeAssert: RecipeAssert = RecipeAssert(baker, recipeInstanceId)
    ```

=== "Java"

    ```java
        RecipeAssert recipeAssert = RecipeAssert.of(baker, recipeInstanceId);
    ```

There is a simple way to assert if the events flow for this recipe instance is exactly the same as expected:

=== "Scala"

    ```scala
      val happyFlow: EventsFlow =
        classOf[SomeSensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow
      RecipeAssert(baker, recipeInstanceId).assertEventsFlow(happyFlow)
    ```

=== "Java"

    ```java
        EventsFlow happyFlow = EventsFlow.of(
            SomeSensoryEvent.class,
            InteractionSucceeded.class
        );
        RecipeAssert.of(baker, recipeInstanceId).assertEventsFlow(happyFlow);
    ```

If the assertion fails a clear error message with the difference is provided:

```
Events are not equal:
    actual: OrderPlaced, ItemsReserved
  expected: OrderPlaced, ItemsNotReserved
difference: ++ ItemsNotReserved
            -- ItemsReserved
```

There are multiple methods to assert ingredient values.

=== "Scala"

    ```scala
    RecipeAssert(baker, recipeInstanceId)
      .assertIngredient("ingredientName").isEqual(expectedValue) // is equal to the expected value
      .assertIngredient("nullishIngredient").isNull // exists and has `null` value
      .assertIngredient("not-existing").isAbsent // ingredient is not a part of the recipe
      .assertIngredient("someListOfStrings").is(value => Assertions.assert(value.asList(classOf[String]).size == 2)) // custom
    ```

=== "Java"

    ```java
    RecipeAssert.of(baker, recipeInstanceId)
      .assertIngredient("ingredientName").isEqual(expectedValue) // is equal to the expected value
      .assertIngredient("nullishIngredient").isNull() // exists and has `null` value
      .assertIngredient("not-existing").isAbsent() // ingredient is not a part of the recipe
      .assertIngredient("someListOfStrings").is(val => Assert.assertEquals(2, val.asList(String.class).size())); // custom
    ```

You can log some information from the baker recipe instance.

_Note: But in most cases you probably should not have to do it because the current state is logged when any of the assertions fail._


=== "Scala"

    ```scala
    RecipeAssert(baker, recipeInstanceId)
        .logIngredients() // logs ingredients
        .logEventNames() // logs event names
        .logVisualState() // logs visual state in dot language
        .logCurrentState() // logs all the information available
    ```

=== "Java"

    ```java
    RecipeAssert.of(baker, recipeInstanceId)
        .logIngredients() // logs ingredients
        .logEventNames() // logs event names
        .logVisualState() // logs visual state in dot language
        .logCurrentState(); // logs all the information available
    ```

Quite a common task is to wait for a baker process to finish or specific event to fire.
Therefore, the blocking method was implemented:

=== "Scala"

    ```scala
    RecipeAssert(baker, recipeInstanceId).waitFor(happyFlow)
    // on this line all the events within happyFlow have happened
    // otherwise timeout occurs and an assertion error is thrown
    ```

=== "Java"

    ```java
    RecipeAssert.of(baker, recipeInstanceId).waitFor(happyFlow);
    // on this line all the events within happyFlow have happened
    // otherwise timeout occurs and an assertion error is thrown
    ```

As you have probably already noticed `RecipeAssert` is chainable
so the typical usage would probably be something like the following:

=== "Scala"

    ```scala
    RecipeAssert(baker, recipeInstanceId)
        .waitFor(happyFlow)
        .assertEventsFlow(happyFlow)
        .assertIngredient("ingredientA").isEqual(ingredientValueA)
        .assertIngredient("ingredientB").isEqual(ingredientValueB)
    ```

=== "Java"

    ```java
    RecipeAssert.of(baker, recipeInstanceId)
        .waitFor(happyFlow)
        .assertEventsFlow(happyFlow)
        .assertIngredient("ingredientA").isEqual(ingredientValueA)
        .assertIngredient("ingredientB").isEqual(ingredientValueB);
    ```
