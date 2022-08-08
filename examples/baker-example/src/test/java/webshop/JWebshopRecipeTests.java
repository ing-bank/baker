package webshop;

import akka.actor.ActorSystem;
import akka.testkit.javadsl.TestKit;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.inmemory.InMemoryBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.EventMoment;
import com.typesafe.config.ConfigFactory;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import scala.Console;
import webshop.simple.*;
import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;

import static org.mockito.Mockito.*;

public class JWebshopRecipeTests {

    static ActorSystem system;
    @BeforeClass
    public static void beforeAll() {
        system = ActorSystem.apply("BakerActorSystem");
    }

    @AfterClass
    public static void afterAll() {
        TestKit.shutdownActorSystem(system);
    }


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

    @Test
    public void shouldRunSimpleInstance() throws ExecutionException, InterruptedException {
        // Compile the recipe
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        List<Object> implementations = ImmutableList.of(
                new MakePaymentInstance(),
                new ReserveItemsInstance(),
                new ShipItemsInstance());

        // Setup the Baker
        Baker baker = AkkaBaker.java(
                ConfigFactory.load(),
                system,
                implementations);

        // Create the sensory events
        List<Item> items = new ArrayList<>(2);
        items.add(new Item("item1"));
        items.add(new Item("item2"));

        EventInstance firstOrderPlaced = EventInstance.from(new JWebshopRecipe.OrderPlaced(items));
        EventInstance paymentInformationReceived = EventInstance.from(new JWebshopRecipe.PaymentInformationReceived(new PaymentInformation("Information")));
        EventInstance shippingInformationReceived = EventInstance.from(new JWebshopRecipe.ShippingAddressReceived(new ShippingAddress("Address")));


        // Run the complete process
        String recipeInstanceId = UUID.randomUUID().toString();
        CompletableFuture<List<String>> result = baker.addRecipe(compiledRecipe, true)
                .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentInformationReceived))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, shippingInformationReceived))
                .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

        // Wait for the results
        List<String> blockedResult = result.get();

        // Validate the results
        assert (blockedResult.contains("OrderPlaced") &&
                blockedResult.contains("PaymentInformationReceived") &&
                blockedResult.contains("ShippingAddressReceived") &&
                blockedResult.contains("ShippingConfirmed"));
    }

    @Test
    public void shouldRunSimpleInstanceMockitoSample() throws InterruptedException, TimeoutException, ExecutionException {
        // Compile the recipe
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JWebshopRecipe.recipe);

        // Setup mock
        ReserveItems reserveItemsMock =
                mock(ReserveItems.class);

        // Setup the Baker
        Baker baker = InMemoryBaker.java(ImmutableList.of(
                new MakePaymentInstance(),
                reserveItemsMock,
                new ShipItemsInstance()));


        // Create the sensory events
        List<Item> items = new ArrayList<>(2);
        items.add(new Item("item1"));
        items.add(new Item("item2"));

        EventInstance firstOrderPlaced = EventInstance.from(new JWebshopRecipe.OrderPlaced(items));
        EventInstance paymentInformationReceived = EventInstance.from(new JWebshopRecipe.PaymentInformationReceived(new PaymentInformation("Information")));
        EventInstance shippingInformationReceived = EventInstance.from(new JWebshopRecipe.ShippingAddressReceived(new ShippingAddress("Address")));

        when(reserveItemsMock.apply(any())).thenReturn(
                new ReserveItems.ItemsReserved(new ReservedItems(items, new byte[20])));

        // Run the complete process
        String recipeInstanceId = UUID.randomUUID().toString();
        CompletableFuture<List<String>> result = baker.addRecipe(compiledRecipe, true)
                .thenCompose(recipeId -> baker.bake(recipeId, recipeInstanceId))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, firstOrderPlaced))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentInformationReceived))
                .thenCompose(ignore -> baker.fireEventAndResolveWhenCompleted(recipeInstanceId, shippingInformationReceived))
                .thenCompose(ignore -> baker.getRecipeInstanceState(recipeInstanceId))
                .thenApply(x -> x.events().stream().map(EventMoment::getName).collect(Collectors.toList()));

        // Wait for the results
        List<String> blockedResult = result.get();

        // Validate the results
        assert (blockedResult.contains("OrderPlaced") &&
                blockedResult.contains("PaymentInformationReceived") &&
                blockedResult.contains("ShippingAddressReceived") &&
                blockedResult.contains("ShippingConfirmed"));
    }


}
