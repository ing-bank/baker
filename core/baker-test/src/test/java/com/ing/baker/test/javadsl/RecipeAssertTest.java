package com.ing.baker.test.javadsl;

import com.ing.baker.runtime.javadsl.EventInstance;
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException;
import com.ing.baker.test.EventsFlow;
import com.ing.baker.test.RecipeAssert;
import com.ing.baker.test.recipe.WebshopBaker;
import com.ing.baker.test.recipe.WebshopRecipe;
import org.junit.Test;
import scala.collection.JavaConverters;
import scala.collection.mutable.Buffer;

import java.util.Arrays;
import java.util.Timer;
import java.util.TimerTask;
import java.util.UUID;

import static org.junit.Assert.assertEquals;

public class RecipeAssertTest {

    private RecipeAssert createRecipeAssert(int delayInSeconds) {
        String recipeInstanceId = UUID.randomUUID().toString();
        WebshopBaker.javaBaker().bake(WebshopBaker.recipeId(), recipeInstanceId);
        Buffer<String> items = JavaConverters.asScalaBuffer(Arrays.asList("item-1", "item-2", "item-3"));

        if (delayInSeconds > 0) {
            new Timer().schedule(
                    new TimerTask() {
                        @Override
                        public void run() {
                            WebshopBaker.javaBaker().fireEvent(recipeInstanceId,
                                    EventInstance.from(new WebshopRecipe.OrderPlaced("order-1", items.toList())));
                        }
                    },
                    delayInSeconds * 1000L
            );
        } else {
            WebshopBaker.javaBaker().fireEvent(recipeInstanceId,
                    EventInstance.from(new WebshopRecipe.OrderPlaced("order-1", items.toList())));
        }

        return RecipeAssert.of(WebshopBaker.javaBaker(), recipeInstanceId);
    }

    private RecipeAssert createRecipeAssert() {
        return createRecipeAssert(0);
    }

    @Test
    public void testHappy() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsFlow(WebshopRecipe.happyFlow());
    }

    @Test
    public void testEventNamesHaveHappened() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventNamesHappened(WebshopRecipe.happyFlow().events().last());
    }

    @Test
    public void testEventsHaveHappened() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsHappened(WebshopRecipe.ItemsReserved.class);
    }

    @Test(expected = AssertionError.class)
    public void testEventNamesHaveNotHappened() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventNamesNotHappened("NonExistentEvent", "NonExistentEvent2");
    }

    @Test(expected = AssertionError.class)
    public void testEventsHaveNotHappened() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsNotHappened(Object.class);
    }

    @Test
    public void testHappyAfterDelay() {
        createRecipeAssert(2)
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsFlow(WebshopRecipe.happyFlow());
    }

    @Test(expected = AssertionError.class)
    public void testFailWithIncorrectEvents() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertEventsFlow(WebshopRecipe.happyFlow().remove(WebshopRecipe.OrderPlaced.class));
    }

    @Test
    public void testAssertIngredientIsEqual() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").isEqual("order-1");
    }

    @Test(expected = AssertionError.class)
    public void testAssertIngredientIsEqualFail() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").isEqual("order-2");
    }

    @Test
    public void testAssertIngredientIsAbsent() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("not-existing").isAbsent();
    }

    @Test(expected = AssertionError.class)
    public void testAssertIngredientIsNull() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").isNull();
    }

    @Test
    public void testAssertIngredientCustom() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").is(value -> assertEquals("order-1", value.as(String.class)));
    }

    @Test(expected = AssertionError.class)
    public void testAssertIngredientCustomFail() {
        createRecipeAssert()
                .waitFor(WebshopRecipe.happyFlow())
                .assertIngredient("orderId").is(value -> assertEquals("order-2", value.as(String.class)));
    }

    @Test(expected = NoSuchProcessException.class)
    public void testNoSuchProcessFailure() {
        EventsFlow flow = EventsFlow.of("Event");
        RecipeAssert.of(WebshopBaker.javaBaker(), UUID.randomUUID().toString())
                .waitFor(flow);
    }
}
