package webshop;

import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.javadsl.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;

public class JMain {

    static public void main(String[] args) {

        ActorSystem actorSystem = ActorSystem.create("WebshopSystem");
        Materializer materializer = ActorMaterializer.create(actorSystem);
        Baker baker = Baker.akkaLocalDefault(actorSystem, materializer);

        List<String> items = new ArrayList<>(2);
        items.add("item1");
        items.add("item2");

        EventInstance firstOrderPlaced =
            EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));
        EventInstance paymentMade =
            EventInstance.from(new JWebshopRecipe.PaymentMade());

        InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        String recipeInstanceId = "first-instance-id";
        CompletableFuture<List<String>> result = baker.addInteractionInstace(reserveItemsInstance)
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
