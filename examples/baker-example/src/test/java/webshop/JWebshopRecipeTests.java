package webshop;

import akka.actor.ActorSystem;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventMoment;
import com.ing.baker.runtime.javadsl.InteractionInstance;
import org.junit.Test;
import scala.Console;
import scala.concurrent.Await;
import webshop.simple.JWebshopRecipe;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;

import static org.mockito.Mockito.*;

public class JWebshopRecipeTests {

    @Test
    public void shouldCompileTheRecipeWithoutIssues() {
        RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
    }

    @Test
    public void shouldVisualizeTheRecipeWithoutIssues() {
        CompiledRecipe recipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);
        String visualization = recipe.getRecipeVisualization();
        System.out.println(Console.GREEN() + "Recipe visualization, paste this into webgraphviz.com:");
        System.out.println(visualization + Console.RESET());
    }

    static public class HappyFlowReserveItems implements JWebshopRecipe.ReserveItems {

        @Override
        public ReserveItemsOutcome apply(String id, List<String> items) {
            return new ItemsReserved(items);
        }
    }

    @Test
    public void shouldRunSimpleInstance() throws ExecutionException, InterruptedException, TimeoutException {
        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        try {

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

            Baker baker = AkkaBaker.javaLocalDefault(actorSystem, Collections.singletonList(reserveItemsInstance));

            String recipeInstanceId = UUID.randomUUID().toString();
            CompletableFuture<List<String>> result = baker.addRecipe(compiledRecipe)
                    .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                    .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                    .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade))
                    .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                    .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

            List<String> blockedResult = result.get();

            assert (blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ItemsReserved"));
        } finally {
            Await.result(actorSystem.terminate(), scala.concurrent.duration.Duration.apply(10, TimeUnit.SECONDS));
        }
    }

    @Test
    public void shouldRunSimpleInstanceMockitoSample() throws InterruptedException, TimeoutException {
        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        try {
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

            Baker baker = AkkaBaker.javaLocalDefault(actorSystem, Collections.singletonList(reserveItemsInstance));

            CompiledRecipe compiledRecipe =
                    RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

            // Add input expectations and their returned event instances
            when(reserveItemsMock.apply("order-uuid", items)).thenReturn(
                    new JWebshopRecipe.ReserveItems.ItemsReserved(items));

            String recipeInstanceId = "first-instance-id";
            CompletableFuture<List<String>> result = baker.addRecipe(compiledRecipe)
                    .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                    .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                    .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade))
                    .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                    .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

            List<String> blockedResult = result.join();

            // Verify that the mock was called with the expected data
            verify(reserveItemsMock).apply("order-uuid", items);

            assert (blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ItemsReserved"));
        } finally {
            Await.result(actorSystem.terminate(), scala.concurrent.duration.Duration.apply(10, TimeUnit.SECONDS));
        }

    }
}
