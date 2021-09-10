package com.ing.baker.test.javadsl;

import akka.actor.ActorSystem;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.InteractionInstance;
import com.ing.baker.test.javadsl.recipe.OrderPlaced;
import com.ing.baker.test.javadsl.recipe.ReserveItemsImpl;
import com.ing.baker.test.javadsl.recipe.WebshopRecipe;
import com.typesafe.config.ConfigFactory;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class BakerAssertTest {

    private static final Baker baker = AkkaBaker.java(ConfigFactory.defaultApplication(), ActorSystem.apply("test"),
            Collections.singletonList(InteractionInstance.from(new ReserveItemsImpl())));

    private static final String recipeId;

    static {
        try {
            recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(WebshopRecipe.RECIPE), true)
                    .get(1, TimeUnit.SECONDS);
        } catch (Exception e) {
            throw new AssertionError("");
        }
    }

    private BakerAssert bakerAssert;
    private String recipeInstanceId;

    @Before
    public void init() throws ExecutionException, InterruptedException, TimeoutException {
        recipeInstanceId = UUID.randomUUID().toString();

        baker.bake(recipeId, recipeInstanceId);

        bakerAssert = BakerAssert.of(baker, recipeInstanceId);
    }

    private void fireSensoryEvent(String orderId) {
        baker.fireEvent(recipeInstanceId, EventInstance.from(new OrderPlaced(orderId,
                Arrays.asList("item-1", "item-2", "item-3"))));
    }

    @Test
    public void testHappy() throws Exception {
        fireSensoryEvent("order-1");
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertEventsFlow(WebshopRecipe.HAPPY_FLOW);
    }

    @Test
    public void testAnotherHappy() {
        fireSensoryEvent("order-2");
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertEventsFlow(WebshopRecipe.HAPPY_FLOW);
    }
}
