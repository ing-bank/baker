package com.ing.baker.test.javadsl;

import akka.actor.ActorSystem;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.javadsl.InteractionInstance;
import com.ing.baker.test.RecipeAssert;
import com.ing.baker.test.javadsl.recipe.OrderPlaced;
import com.ing.baker.test.javadsl.recipe.ReserveItemsImpl;
import com.ing.baker.test.javadsl.recipe.WebshopRecipe;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.TimeUnit;

public class RecipeAssertTest {

    private static final Baker baker = AkkaBaker.javaLocalDefault(ActorSystem.apply(),
            Collections.singletonList(InteractionInstance.from(new ReserveItemsImpl())));

    private final String recipeInstanceId = UUID.randomUUID().toString();

    @Before
    public void init() throws Exception {
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.RECIPE);
        String recipeId = baker.addRecipe(compiledRecipe, false).get(10, TimeUnit.SECONDS);
        baker.bake(recipeId, recipeInstanceId);
        baker.fireEvent(recipeInstanceId,
                EventInstance.from(new OrderPlaced("order-1", Arrays.asList("item-1", "item-2", "item-3"))));
    }

    @Test
    public void testHappy() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .logEventNames()
                .logIngredients()
                .logVisualState()
                .assertEventsFlow(WebshopRecipe.HAPPY_FLOW);
    }

    @Test(expected = AssertionError.class)
    public void testHappyFail() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertEventsFlow(WebshopRecipe.HAPPY_FLOW.remove(OrderPlaced.class));
    }

    @Test
    public void testAssertIngredientIsEqual() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("orderId").isEqual("order-1");
    }

    @Test(expected = AssertionError.class)
    public void testAssertIngredientIsEqualFail() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("orderId").isEqual("order-2");
    }

    @Test
    public void testAssertIngredientIsAbsent() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("not-existing").isAbsent();
    }

    @Test
    public void testAssertIngredientCustom() {
        RecipeAssert.of(baker, recipeInstanceId)
                .waitFor(WebshopRecipe.HAPPY_FLOW)
                .assertIngredient("orderId").is(val -> Assert.assertEquals("order-1", val.as(String.class)));
    }
}
