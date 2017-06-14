package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.javadsl.events.InitialSensoryEvent;
import com.ing.baker.recipe.javadsl.interactions.*;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static org.junit.Assert.assertEquals;

public class RecipeTest extends JavadslTestHelper {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupRecipeWithProvidesIngredientInteraction() {
        Recipe recipe = new Recipe("ProvidesIngredientInteractionRecipe")
                .withInteraction(of(ProvidesIngredientInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getInteractions().get(0).interaction(), providesIngredientInteraction);
    }

    @Test
    public void shouldSetupRecipeWithRequiredProcessIdStringInteraction() {
        Recipe recipe = new Recipe("RequiredProcessIdStringInteractionRecipe")
                .withInteraction(of(RequiresProcessIdStringInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        System.out.println(recipe.getInteractions().get(0).interaction().inputIngredients());
        assertEquals(recipe.getInteractions().get(0).interaction(), requiresProcessIdStringInteraction);
    }

    @Test
    public void shouldSetupRecipeWithRequiredProcessIdUUIDInteraction() {
        Recipe recipe = new Recipe("RequiredProcessIdUUIDInteractionRecipe")
                .withInteraction(of(RequiresProcessIdUUIDInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getInteractions().get(0).interaction(), requiresProcessIdUUIDInteraction);
    }

    @Test
    public void shouldSetupRecipeWithFiresEventInteraction() {
        Recipe recipe = new Recipe("FiresEventInteractionRecipe")
                .withInteraction(of(FiresEventInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getInteractions().get(0).interaction(), firesEventInteractionCheck);
    }

    @Test
    public void shouldSetupRecipeWithFiresTwoEventsInteraction() {
        Recipe recipe = new Recipe("FiresTwoEventInteractionRecipe")
                .withInteraction(of(FiresTwoEventInteraction.class));
        assertEquals(recipe.getEvents().size(), 0);
        assertEquals(recipe.getInteractions().size(), 1);
        assertEquals(recipe.getInteractions().get(0).interaction(), firesTwoEventInteractionCheck);
    }

    @Test
    public void shouldSetupRecipeWithASensoryEvent() {
        Recipe recipe = new Recipe("SensoryEventRecipe")
                .withSensoryEvent(InitialSensoryEvent.class);
        assertEquals(recipe.getEvents().size(), 1);
        assertEquals(recipe.getInteractions().size(), 0);
        assertEquals(recipe.getEvents().get(0), initialSensoryEventCheck);
    }
}
