package webshop;

import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventResult;
import com.ing.baker.runtime.javadsl.InteractionInstance;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;

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

        InteractionInstance reserveItemsInstance = InteractionInstance.from(new ReserveItems());
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        String recipeInstanceId = "first-instance-id";
        CompletableFuture<List<String>> result = baker.addImplementation(reserveItemsInstance)
            .thenCompose(ignore -> baker.addRecipe(compiledRecipe))
            .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
            .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
            .thenApply(EventResult::events);

        List<String> blockedResult = result.join();
        assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("ReservedItems"));
    }
}
