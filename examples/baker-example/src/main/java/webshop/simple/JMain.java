package webshop.simple;

import akka.actor.ActorSystem;
import com.datastax.oss.driver.shaded.guava.common.collect.ImmutableList;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.inmemory.InMemoryBaker;
import com.ing.baker.runtime.javadsl.*;
import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ShippingAddress;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

public class JMain {

  public static void main(String[] args) throws ExecutionException, InterruptedException {
      ActorSystem actorSystem = ActorSystem.create("WebshopSystem");

      Baker baker = InMemoryBaker.java(
              ImmutableList.of(
                      new ReserveItemsInstance())
      );

      List<Item> items = new ArrayList<>(2);
      items.add(new Item("item1"));
      items.add(new Item("item2"));

      EventInstance firstOrderPlaced =
          EventInstance.from(new JWebshopRecipe.OrderPlaced("order-uuid", items));
      EventInstance paymentInformationReceived =
          EventInstance.from(new JWebshopRecipe.PaymentInformationReceived(new PaymentInformation("Payment information")));
      EventInstance shippingAddressReceived =
              EventInstance.from(new JWebshopRecipe.ShippingAddressReceived(new ShippingAddress("Address")));

      CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

      BiConsumer<String, EventInstance> handler = (String recipeInstanceId, EventInstance event) ->
          System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event.name());
      baker.registerEventListener(handler);

      baker.registerBakerEventListener((BakerEvent event) -> System.out.println(event));

      String recipeInstanceId = "first-instance-id";
      CompletableFuture<List<String>> result = baker.addRecipe(compiledRecipe, true)
          .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
          .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
          .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentInformationReceived))
          .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, shippingAddressReceived))
          .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
          .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

      List<String> blockedResult = result.join();
      assert(blockedResult.contains("OrderPlaced") && blockedResult.contains("PaymentMade") && blockedResult.contains("ReservedItems"));

      System.out.println("Events fired" + baker.getEventNames(recipeInstanceId).get());

    }
}
