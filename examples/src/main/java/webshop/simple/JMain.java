package webshop.simple;

import akka.actor.ActorSystem;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.javadsl.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

public class JMain {

    static public void main_ignore(String[] args) {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Baker baker = Baker.akkaLocalDefault(actorSystem);

        List<String> items = new ArrayList<>(2);
        items.add("item1");
        items.add("item2");

        EventInstance firstOrderPlaced =
            EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));
        EventInstance paymentMade =
            EventInstance.from(new JWebshopRecipe.PaymentMade());

        InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItemsInstance());
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        BiConsumer<String, EventInstance> handler = (String recipeInstanceId, EventInstance event) ->
            System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event.name());
        baker.registerEventListener(handler);

        baker.registerBakerEventListener((BakerEvent event) -> System.out.println(event));

        String recipeInstanceId = "first-instance-id";
        CompletableFuture<List<String>> result = baker.addInteractionInstance(reserveItemsInstance)
            .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
            .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
            .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
            .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade))
            .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
            .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

        List<String> blockedResult = result.join();
        assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ReservedItems"));
    }
}
