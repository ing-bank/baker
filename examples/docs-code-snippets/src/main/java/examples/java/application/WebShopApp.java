package examples.java.application;

import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.runtime.inmemory.InMemoryBaker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;
import examples.java.ingredients.Address;
import examples.java.interactions.CancelOrderImpl;
import examples.java.interactions.CheckStockImpl;
import examples.java.interactions.ShipOrderImpl;
import examples.java.recipes.WebShopRecipe;

import java.time.Duration;
import java.util.List;
import java.util.UUID;
import java.util.concurrent.ExecutionException;

public class WebShopApp {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        var baker = InMemoryBaker.java(
            List.of(new CheckStockImpl(), new CancelOrderImpl(), new ShipOrderImpl())
        );

        var recipeInstanceId = UUID.randomUUID().toString();
        var sensoryEvent = EventInstance.from(createOrderPlaced());

        var recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(WebShopRecipe.recipe), true).get();
        baker.bake(recipeId, recipeInstanceId).get();
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent).get();
        baker.awaitCompleted(recipeInstanceId, Duration.ofSeconds(5)).get();
    }

    private static OrderPlaced createOrderPlaced() {
        var address = new Address("Hoofdstraat", "Amsterdam", "1234AA", "The Netherlands");
        return new OrderPlaced("123", "456", address, List.of("iPhone", "Playstation5"));
    }
}
