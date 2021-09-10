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
import com.ing.baker.types.Value;
import com.typesafe.config.ConfigFactory;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.TimeUnit;

public class BakerAssertTest {

    private static final Baker baker = AkkaBaker.java(ConfigFactory.defaultApplication(), ActorSystem.apply("test"),
            Collections.singletonList(InteractionInstance.from(new ReserveItemsImpl())));

    private static final String recipeId;

    static {
        try {
            recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(WebshopRecipe.RECIPE), true)
                    .get(10, TimeUnit.SECONDS);
        } catch (Exception e) {
            throw new AssertionError(e);
        }
    }

    private BakerAssert bakerAssert;

    @Before
    public void init() {
        String recipeInstanceId = UUID.randomUUID().toString();

        baker.bake(recipeId, recipeInstanceId);

        bakerAssert = BakerAssert.of(baker, recipeInstanceId);

        baker.fireEvent(recipeInstanceId, EventInstance.from(new OrderPlaced("order-1",
                Arrays.asList("item-1", "item-2", "item-3"))));
    }

    @Test
    public void testHappy() {
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .logEventNames()
                .logIngredients()
                .logVisualState()
                .assertEventsFlow(WebshopRecipe.HAPPY_FLOW);
    }

    @Test
    public void testHappyFail() {
        boolean failed = false;
        try {
            bakerAssert
                    .waitFor(WebshopRecipe.HAPPY_FLOW)
                    .assertEventsFlow(WebshopRecipe.HAPPY_FLOW.removeClass(OrderPlaced.class));
        } catch (AssertionError e) {
            // expected
            failed = true;
        }
        Assert.assertTrue(failed);
    }

    @Test
    public void testAssertIngredientIsEqual() {
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("orderId").isEqual("order-1");
    }

    @Test
    public void testAssertIngredientIsEqualFail() {
        boolean failed = false;
        try {
            bakerAssert
                    .waitFor(WebshopRecipe.HAPPY_FLOW)
                    .assertIngredient("orderId").isEqual("order-2");
        } catch (AssertionError e) {
            // expected
            failed = true;
        }
        Assert.assertTrue(failed);
    }

    @Test
    public void testAssertIngredientIsNull() {
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("not-existing").isNull();
    }

    // FIXME why "value.as(String.class)" does not compile here????
    @Test
    public void testAssertIngredientCustom() {
        bakerAssert
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("orderId").is(val -> Assert.assertEquals("order-1", ((Value)val).as(String.class)));
    }
}
