package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.common.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithIngredient;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithoutIngredient;
import com.ing.baker.recipe.javadsl.interactions.FiresTwoEventInteraction;
import com.ing.baker.recipe.javadsl.interactions.ProvidesIngredientInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdUUIDInteraction;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.time.Duration;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static com.ing.baker.recipe.javadsl.JavadslTestHelper.*;
import static org.junit.Assert.assertEquals;

public class RecipeTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupRecipeWithOneInteractionDescriptor() {
        Recipe recipe = new Recipe("OneInteractionRecipe")
                .withInteraction(of(ProvidesIngredientInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getInteractions().get(0).interaction(), providesIngredientInteractionCheck());
    }

    @Test
    public void shouldSetupRecipeWithMultipleInteractionDescriptors() {
        Recipe recipe = new Recipe("MultipleInteractionsRecipe")
                .withInteractions(
                        of(RequiresProcessIdUUIDInteraction.class),
                        of(FiresTwoEventInteraction.class),
                        of(ProvidesIngredientInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 3);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getInteractions().get(0).interaction(), requiresProcessIdUUIDInteractionCheck());
        assertEquals(recipe.getInteractions().get(1).interaction(), firesTwoEventInteractionCheck());
        assertEquals(recipe.getInteractions().get(2).interaction(), providesIngredientInteractionCheck());
    }

    @Test
    public void shouldSetupRecipeWithOneSieveDescriptor() {
        Recipe recipe = new Recipe("OneSieveRecipe")
                .withSieve(of(ProvidesIngredientInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 1);
        assertEquals(recipe.getSieves().get(0).interaction(), providesIngredientInteractionCheck());
    }

    @Test
    public void shouldSetupRecipeWithMultipleSieveDescriptors() {
        Recipe recipe = new Recipe("MultipleInteractionsRecipe")
                .withSieves(
                        of(RequiresProcessIdUUIDInteraction.class),
                        of(FiresTwoEventInteraction.class),
                        of(ProvidesIngredientInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 3);
        assertEquals(recipe.getSieves().get(0).interaction(), requiresProcessIdUUIDInteractionCheck());
        assertEquals(recipe.getSieves().get(1).interaction(), firesTwoEventInteractionCheck());
        assertEquals(recipe.getSieves().get(2).interaction(), providesIngredientInteractionCheck());
    }

    @Test
    public void shouldSetupRecipeWithOneSensoryEvent() {
        Recipe recipe = new Recipe("OneSensoryEventRecipe")
                .withSensoryEvent(SensoryEventWithIngredient.class);
        assertEquals(recipe.getEvents().size(), 1);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getEvents().get(0), sensoryEventWithIngredientCheck());
    }

    @Test
    public void shouldSetupRecipeWithMultipleSensoryEvent() {
        Recipe recipe = new Recipe("MultipleSensoryEventRecipe")
                .withSensoryEvents(
                        SensoryEventWithIngredient.class,
                        SensoryEventWithoutIngredient.class);
        assertEquals(recipe.getEvents().size(), 2);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getEvents().get(0), sensoryEventWithIngredientCheck());
        assertEquals(recipe.getEvents().get(1), sensoryEventWithoutIngredientCheck());
    }

    @Test
    public void shouldBeAbleToAddARecipeToARecipe() {
        Recipe subRecipe = new Recipe("OneSensoryEventRecipe")
                .withSensoryEvent(SensoryEventWithIngredient.class)
                .withInteraction(of(ProvidesIngredientInteraction.class));
        Recipe recipe = new Recipe("OneInteractionRecipe")
                .withInteraction(of(FiresTwoEventInteraction.class))
                .withSensoryEvent(SensoryEventWithoutIngredient.class)
                .withRecipe(subRecipe);
        assertEquals(recipe.getEvents().size(), 1);
        assertEquals(recipe.getInteractions().size(), 2);
    }

    @Test
    public void shouldSetupRecipeWithDefaultBlockedFailureStrategy() {
        Recipe recipe = new Recipe("defaultBlockedFailureStrategyRecipe");
        assertEquals(InteractionFailureStrategy.BlockInteraction$.class, recipe.defaultFailureStrategy().getClass());
    }

    @Test
    public void shouldUpdateFailureStrategy() {
        Recipe recipe = new Recipe("retryWithIncrementalBackoffFailureStrategyRecipe")
                .withDefaultRetryFailureStrategy(Duration.ofMillis(100), Duration.ofHours(24));
        assertEquals(InteractionFailureStrategy.RetryWithIncrementalBackoff.class, recipe.defaultFailureStrategy().getClass());

        recipe = new Recipe("retryWithIncrementalBackoffFailureStrategyRecipe2")
                .withDefaultRetryFailureStrategy(Duration.ofMillis(100), 1.5, 200);
        assertEquals(InteractionFailureStrategy.RetryWithIncrementalBackoff.class, recipe.defaultFailureStrategy().getClass());
    }
}
