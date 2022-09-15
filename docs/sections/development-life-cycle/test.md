# Test

The Baker model already enforces separation and decoupling between parts of your system, which eases testability, it 
presents a model that divides units of code into modularized sections, more specifically, it provides a clear distinction
between business logic and implementation through the `Recipe` and `InteractionImplementations`, and independence between 
`Interactions`, since every `Interaction` should only depend on the input. 

We present the layers of testing when using Baker, and how to write tests for such layers, use them as necessary.
We also will explain how to simplify your testing logic using our `baker-test` library.

## Testing Recipes for Soundness: Compiling the Recipe in a Test

First, one important notice is that currently Baker does not check at compile time the soundness of your Recipe (if your
Recipe makes any sense), but it does so when compiling it with the `RecipeCompiler.compileRecipe(recipe)` API. Errors are 
thrown in the form of exceptions describing the issue. So a simple unit test that simply compiles your `Recipe` is essential.

=== "Scala"

    ```scala 
    class WebshopRecipeSpec extends FlatSpec with Matchers {

      "The WebshopRecipe" should "compile the recipe without errors" in {
        RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
      }
    }
    ```

=== "Java"

    ```java 
    public class JWebshopRecipeTests {

        @Test
        public void shouldCompileTheRecipeWithoutIssues() {
            RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
        }
    }
    ```

## Testing Recipes for Correctness: Mocking Interaction Implementations

The next layer is to test that the Recipe actually does what you expect it to do at the business logic level **independently**
of the underlying implementations. One way of doing so is by providing `InteractionImplementations` that behave as expected
according to a testing scenario. 

On the next example we will:

1. Create a new local instance of baker.
2. Setup mocked interaction instances that behave according to your desired test scenario.
3. Wire the recipe and implementations to fire sensory events according to your desired test scenario.
4. Inspect the recipe instance state.
5. Assert expectations on the state and/or the sensory event results.

_Note: Take into consideration the asynchronous nature of Baker, some times the easiest is to use `fireAndResolveWhenCompleted`
that will resolve when a sensory event has completely finished affecting the state of the recipe instance.
Or the other way is to use `BakerAssert.waitFor(eventsFlow)` method from the `baker-test` library._

=== "Scala"

    ```scala 

    /** Interface used to mock the ReserveItems interaction using the reflection API. */
    trait ReserveItems {

      def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
    }

    /** Mock of the ReserveItems interaction. */
    class ReserveItemsMock extends ReserveItems {

      override def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] =
        Future.successful(WebshopRecipeReflection.ItemsReserved(items))
    }

    "The Webshop Recipe" should "reserve items in happy conditions" in {

      val system: ActorSystem = ActorSystem("baker-webshop-system")
      val baker: Baker =  AkkaBaker.localDefaul(system)

      val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
      val recipeInstanceId: String = UUID.randomUUID().toString

      val orderId: String = "order-id"
      val items: List[String] = List("item1", "item2")

      val orderPlaced = EventInstance
        .unsafeFrom(WebshopRecipeReflection.OrderPlaced(orderId, items))
      val paymentMade = EventInstance
        .unsafeFrom(WebshopRecipeReflection.PaymentMade())

      val reserveItemsInstance: InteractionInstance =
        InteractionInstance.unsafeFrom(new ReserveItemsMock)

      for {
        _ <- baker.addInteractionInstace(reserveItemsInstance)
        recipeId <- baker.addRecipe(RecipeRecord.of(compiled))
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(
          recipeInstanceId, orderPlaced)
        _ <- baker.fireEventAndResolveWhenCompleted(
          recipeInstanceId, paymentMade)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        provided = state
          .ingredients
          .find(_._1 == "reservedItems")
          .map(_._2.as[List[String]])
          .map(_.mkString(", "))
          .getOrElse("No reserved items")
      } yield provided shouldBe items.mkString(", ")
    }
    ``` 

=== "Java"

    ```java 
    static public class HappyFlowReserveItems implements JWebshopRecipe.ReserveItems {

        @Override
        public ReserveItemsOutcome apply(String id, List<String> items) {
            return new ItemsReserved(items);
        }
    }

    @Test
    public void shouldRunSimpleInstance() {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Baker baker = AkkaBaker.javaLocalDefault(actorSystem);

        List<String> items = new ArrayList<>(2);
        items.add("item1");
        items.add("item2");

        EventInstance firstOrderPlaced =
                EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));
        EventInstance paymentMade =
                EventInstance.from(new JWebshopRecipe.PaymentMade());

        InteractionInstance reserveItemsInstance =
                InteractionInstance.from(new HappyFlowReserveItems());
        CompiledRecipe compiledRecipe =
                RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        String recipeInstanceId = "first-instance-id";
        CompletableFuture<List<String>> result = baker.addInteractionInstace(reserveItemsInstance)
                .thenCompose(ignore -> baker.addRecipe(RecipeRecord.of(compiledRecipe)))
                .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade))
                .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

        List<String> blockedResult = result.join();

        assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ItemsReserved"));
    }
    ```

This test is replicating a full round through a `Recipe`, the only difference with your normal production code is that 
`InteractionInstances` are adapted to fit the scenario you want to check, so the objective here is to test that the `Recipe`
ends on the desired state given a certain order of firing sensory events and that the interaction instances return the
specific data.

_Note: We recommend you abstract away these scenarios with a function that will run them given different 
interaction instances, so that you can run the same scenario on different environments, like when you want to do a E2E
on a test environment._

## Mocking Interaction Implementations with Mockito

Baker supports `InteractionInstances` that are [mockito](https://site.mockito.org/) mocks, this will give you the added 
semantics of Mockito, like verifying that the interaction instance was called, or even called with the expected data.

=== "Scala"

    ```scala  

    trait ReserveItems {

      def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
    }


    "The Webshop Recipe" should "reserve items in happy conditions (mockito)" in {

      val system: ActorSystem = ActorSystem("baker-webshop-system")
      val baker: Baker = AkkaBaker.localDefault(system)

      val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
      val recipeInstanceId: String = UUID.randomUUID().toString

      val orderId: String = "order-id"
      val items: List[String] = List("item1", "item2")

      val orderPlaced = EventInstance
        .unsafeFrom(WebshopRecipeReflection.OrderPlaced(orderId, items))
      val paymentMade = EventInstance
        .unsafeFrom(WebshopRecipeReflection.PaymentMade())

      // The ReserveItems interaction being mocked by Mockito
      val mockedReserveItems: ReserveItems = mock[ReserveItems]
      val reserveItemsInstance: InteractionInstance =
        InteractionInstance.unsafeFrom(mockedReserveItems)

      when(mockedReserveItems.apply(orderId, items))
        .thenReturn(Future.successful(WebshopRecipeReflection.ItemsReserved(items)))

      for {
        _ <- baker.addInteractionInstace(reserveItemsInstance)
        recipeId <- baker.addRecipe(RecipeRecord.of(compiled))
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(
          recipeInstanceId, orderPlaced)
        _ <- baker.fireEventAndResolveWhenCompleted(
          recipeInstanceId, paymentMade)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        provided = state
          .ingredients
          .find(_._1 == "reservedItems")
          .map(_._2.as[List[String]])
          .map(_.mkString(", "))
          .getOrElse("No reserved items")

        // Verify that the mock was called with the expected data
        _ = verify(mockedReserveItems).apply(orderId, items)
      } yield provided shouldBe items.mkString(", ")
    }
    ```

=== "Java"

    ```java  
    import static org.mockito.Mockito.*;

    @Test
    public void shouldRunSimpleInstanceMockitoSample() {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Baker baker = AkkaBaker.javaLocalDefault(actorSystem);

        List<String> items = new ArrayList<>(2);
        items.add("item1");
        items.add("item2");

        EventInstance firstOrderPlaced =
                EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));
        EventInstance paymentMade =
                EventInstance.from(new JWebshopRecipe.PaymentMade());

        // The ReserveItems interaction being mocked by Mockito
        JWebshopRecipe.ReserveItems reserveItemsMock =
                mock(JWebshopRecipe.ReserveItems.class);
        InteractionInstance reserveItemsInstance =
                InteractionInstance.from(reserveItemsMock);
        CompiledRecipe compiledRecipe =
                RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        // Add input expectations and their returned event instances
        when(reserveItemsMock.apply("order-uuid", items)).thenReturn(
                new JWebshopRecipe.ReserveItems.ItemsReserved(items));

        String recipeInstanceId = "first-instance-id";
        CompletableFuture<List<String>> result = baker.addInteractionInstace(reserveItemsInstance)
                .thenCompose(ignore -> baker.addRecipe(RecipeRecord.of(compiledRecipe)))
                .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade))
                .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

        List<String> blockedResult = result.join();

        // Verify that the mock was called with the expected data
        verify(reserveItemsMock).apply("order-uuid", items);

        assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ItemsReserved"));
    }
    ```

## Testing Individual Implementations

The final layer is to individually test your implementations, which will resemble your normal e2e tests, interconnectivity 
tests, or unit tests which mock the dependencies. If we put a code example here it would be more of a tutorial on how to 
generally test code than Baker, which is a good argument to show that Baker si all about decoupling your code and automatically
orchestrate it through distributed boundaries.

## Baker Test library

This library contains the tooling to help with the testing of the baker-based logic. 
The usage of this library makes the test code concise and readable in both java and scala. 
It also simplifies the testing of the cases when asynchronous recipe execution is involved.

=== "Scala"

    ```scala
    RecipeAssert(baker, recipeInstanceId)
        .waitFor(classOf[SensoryEvent] :: classOf[InteractionSucceeded] :: EmptyFlow)
        .assertIngredient("testIngredient").isEqual("foo")
    ```

=== "Java"

    ```java
    RecipeAssert.of(baker, recipeInstanceId)
        .waitFor(EventsFlow.of(SensoryEvent.class, InteractionSucceeded.class))
        .assertIngredient("testIngredient").isEqual("foo")
    ```

You can include it to your project by adding `baker-test` artifact:

=== "Sbt"

    ```scala 
    libraryDependencies += "com.ing.baker" %% "baker-test" % bakerVersion
    ```

=== "Maven"

    ```xml 
    <dependency>
      <groupId>com.ing.baker</groupId>
      <artifactId>baker-test_2.12</artifactId>
      <version>${baker.version}</version>
      <scope>test</scope>
    </dependency>
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