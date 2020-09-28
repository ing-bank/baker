# Test

The Baker model already enforces separation and decoupling between parts of your system, which eases testability, it 
presents a model that divides units of code into modularized sections, more specifically, it provides a clear distinction
between business logic and implementation through the `Recipe` and `InteractionImplementations`, and independence between 
`Interactions`, since every `Interaction` should only depend on the input. 

We present the layers of testing when using Baker, and how to write tests for such layers, use them as necessary.

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
that will resolve when a sensory event has completely finished affecting the state of the recipe instance._

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
        recipeId <- baker.addRecipe(compiled)
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
                .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
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
        recipeId <- baker.addRecipe(compiled)
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
                .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
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
