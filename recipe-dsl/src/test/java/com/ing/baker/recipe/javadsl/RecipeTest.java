package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.javadsl.events.SensoryEventWithIngredient;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithoutIngredient;
import com.ing.baker.recipe.javadsl.interactions.FiresTwoEventInteraction;
import com.ing.baker.recipe.javadsl.interactions.SimpleInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdStringInteraction;
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
                .withInteraction(of(SimpleInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getSieves().size(), 0);
    }

    @Test
    public void shouldSetupRecipeWithMultipleInteractionDescriptors() {
        Recipe recipe = new Recipe("MultipleInteractionsRecipe")
                .withInteractions(
                        of(RequiresProcessIdStringInteraction.class),
                        of(FiresTwoEventInteraction.class),
                        of(SimpleInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 3);
        assertEquals(recipe.getSieves().size(), 0);
    }

    @Test
    public void shouldSetupRecipeWithOneSieveDescriptor() {
        Recipe recipe = new Recipe("OneSieveRecipe")
                .withSieve(of(SimpleInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 1);
    }

    @Test
    public void shouldSetupRecipeWithMultipleSieveDescriptors() {
        Recipe recipe = new Recipe("MultipleInteractionsRecipe")
                .withSieves(
                        of(RequiresProcessIdStringInteraction.class),
                        of(FiresTwoEventInteraction.class),
                        of(SimpleInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 3);
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
    public void shouldSetupRecipeWithSensoryEventWithMaxFiringLimit() {
        Recipe recipe = new Recipe("EventWithMaxFiringLimitRecipe")
                .withSensoryEvent(SensoryEventWithIngredient.class, 1)
                .withSensoryEvent(SensoryEventWithoutIngredient.class, 2);

        assertEquals(recipe.getEvents().size(), 2);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getEvents().get(0), sensoryEventWithIngredientCheck());
        assertEquals(recipe.getEvents().get(1), sensoryEventWithoutIngredientCheck());
        assertEquals(recipe.getEvents().get(0).maxFiringLimit().get(), new Integer(1));
        assertEquals(recipe.getEvents().get(1).maxFiringLimit().get(), new Integer(2));
    }

    @Test
    public void shouldSetupRecipeWithSensoryEventNoMaxFiringLimit() {
        Recipe recipe = new Recipe("EventWithMaxFiringLimitRecipe")
                .withSensoryEventsNoFiringLimit(
                        SensoryEventWithIngredient.class,
                        SensoryEventWithoutIngredient.class);

        assertEquals(recipe.getEvents().size(), 2);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getSieves().size(), 0);
        assertEquals(recipe.getEvents().get(0), sensoryEventWithIngredientCheck());
        assertEquals(recipe.getEvents().get(1), sensoryEventWithoutIngredientCheck());
        assertEquals(recipe.getEvents().get(0).maxFiringLimit(), scala.Option.empty());
        assertEquals(recipe.getEvents().get(1).maxFiringLimit(), scala.Option.empty());
    }

    @Test
    public void shouldBeAbleToAddARecipeToARecipe() {
        Recipe subRecipe = new Recipe("OneSensoryEventRecipe")
                .withSensoryEvent(SensoryEventWithIngredient.class)
                .withInteraction(of(SimpleInteraction.class));
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
        assertEquals(
                com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction.class,
                recipe.defaultFailureStrategy().getClass());
    }

    @Test
    public void shouldUpdateFailureStrategy() {
        Recipe recipe = new Recipe("retryWithIncrementalBackoffFailureStrategyRecipe")
                .withDefaultFailureStrategy(
                       new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                                .withInitialDelay(Duration.ofMillis(100))
                                .withDeadline(Duration.ofHours(24))
                                .build());
        assertEquals(
                com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.class,
                recipe.defaultFailureStrategy().getClass());

        Recipe recipe2 = new Recipe("retryWithIncrementalBackoffFailureStrategyRecipe2")
                .withDefaultFailureStrategy(
                        new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                                .withInitialDelay(Duration.ofMillis(100))
                                .withDeadline(Duration.ofHours(24))
                                .build()
                );
        assertEquals(
                com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.class,
                recipe2.defaultFailureStrategy().getClass());

        Recipe recipe3 = new Recipe("retryWithIncrementalBackoffFailureStrategyRecipe3")
                .withDefaultFailureStrategy(
                        InteractionFailureStrategy.BlockInteraction());
        assertEquals(
                com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction.class,
                recipe3.defaultFailureStrategy().getClass());
    }
}
