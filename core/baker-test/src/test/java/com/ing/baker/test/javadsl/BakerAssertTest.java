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
import org.junit.Assert;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.TimeUnit;

public class BakerAssertTest {

    private final Baker baker = AkkaBaker.java(ConfigFactory.defaultApplication(), ActorSystem.apply("test"),
            Collections.singletonList(InteractionInstance.from(new ReserveItemsImpl())));

    private BakerAssert createBakerAssert() throws Exception {
        String recipeInstanceId = UUID.randomUUID().toString();

        String recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(WebshopRecipe.TEST_RECIPE), true).get(1, TimeUnit.SECONDS);

        baker.bake(recipeId, recipeInstanceId);

        baker.fireEvent(recipeInstanceId, EventInstance.from(new OrderPlaced("order-1",
                Arrays.asList("item-1", "item-2", "item-3"))));

        return BakerAssert.of(baker, recipeInstanceId);
    }

    @Test
    public void test() throws Exception {
        BakerAssert bakerAssert = createBakerAssert();
        Assert.assertNotNull(bakerAssert);

        BakerEventsFlow happyFlow = BakerEventsFlow.of("OrderPlaced", "ItemsReserved");
        bakerAssert
                .waitFor(happyFlow)
                .assertEventsFlow(happyFlow);
    }
}
