package com.ing.baker.test.javadsl;

import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.test.RecipeAssert;
import com.ing.baker.test.recipe.WebshopBaker;
import com.ing.baker.test.recipe.WebshopRecipe;
import org.junit.Before;
import org.junit.Test;
import scala.collection.JavaConverters;
import scala.collection.mutable.Buffer;

import java.util.Arrays;
import java.util.UUID;

import static org.junit.Assert.assertEquals;

public class RecipeAssertTest {

    private String recipeInstanceId;

    @Before
    public void init() {
        recipeInstanceId = UUID.randomUUID().toString();
        WebshopBaker.javaBaker().bake(WebshopBaker.recipeId(), recipeInstanceId);
        Buffer<String> items = JavaConverters.asScalaBuffer(Arrays.asList("item-1", "item-2", "item-3"));
        WebshopBaker.javaBaker().fireEvent(recipeInstanceId,
                EventInstance.from(new WebshopRecipe.OrderPlaced("order-1", items.toList())));
    }

    @Test
    public void testHappy() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .logEventNames()
                .logIngredients()
                .logVisualState()
                .assertEventsFlow(WebshopRecipe.happyFlow());
    }

    @Test(expected = AssertionError.class)
    public void testHappyFail() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsFlow(WebshopRecipe.happyFlow().remove(WebshopRecipe.OrderPlaced.class));
    }

    @Test
    public void testAssertIngredientIsEqual() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").isEqual("order-1");
    }

    @Test(expected = AssertionError.class)
    public void testAssertIngredientIsEqualFail() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").isEqual("order-2");
    }

    @Test
    public void testAssertIngredientIsAbsent() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("not-existing").isAbsent();
    }

    @Test
    public void testAssertIngredientCustom() {
        RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId)
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").is(value -> assertEquals("order-1", value.as(String.class)));
    }
}
