package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.javadsl.events.SensoryEventWithIngredient;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithoutIngredient;
import com.ing.baker.recipe.javadsl.interactions.ProvidesIngredientInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdStringInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdUUIDInteraction;
import org.junit.Test;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static com.ing.baker.recipe.javadsl.JavadslTestHelper.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class InteractionDescriptorTest {

    @Test
    public void shouldCreateInteractionDescriptorOfProvidesIngredientInteraction() {
        com.ing.baker.recipe.common.InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class);
        assertEquals(providesIngredientInteractionCheck(), interactionDescriptor.interaction());
    }

    @Test
    public void shouldCreateInteractionDescriptorOfRequiredProcessIdStringInteraction() {
        com.ing.baker.recipe.common.InteractionDescriptor interactionDescriptor = of(RequiresProcessIdStringInteraction.class);
        assertEquals(requiresProcessIdStringInteractionCheck(), interactionDescriptor.interaction());
    }

    @Test
    public void shouldCreateInteractionDescriptorOfRequiredProcessIdUUIDInteraction() {
        InteractionDescriptor interactionDescriptor = of(RequiresProcessIdUUIDInteraction.class);
        assertEquals(requiresProcessIdUUIDInteractionCheck(), interactionDescriptor.interaction());
    }

    @Test
    public void shouldCreateInteractionDescriptorWithDefaultName() {
        InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class);
        assertEquals("ProvidesIngredientInteraction", interactionDescriptor.name());
    }

    @Test
    public void shouldCreateInteractionDescriptorWithChangedName() {
        InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class, "ChangedName");
        assertEquals("ChangedName", interactionDescriptor.name());
    }

    @Test
    public void shouldCreateInteractionDefaultWithInteractionActionType() {
        InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class);
        assertEquals(com.ing.baker.recipe.common.InteractionAction$.class, interactionDescriptor.actionType().getClass());
    }

    @Test
    public void shouldUpdateTheRequiredEventList() {
        InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class);
        assertTrue(interactionDescriptor.requiredEvents().isEmpty());

        InteractionDescriptor interactionDescriptorWithRequiredEvent =
                interactionDescriptor.withRequiredEvent(SensoryEventWithIngredient.class);

        assertEquals(interactionDescriptorWithRequiredEvent.requiredEvents().size(), 1);
        assertTrue(interactionDescriptorWithRequiredEvent.requiredEvents().contains(sensoryEventWithIngredientCheck()));

        InteractionDescriptor interactionDescriptorWithRequiredEvents =
                interactionDescriptor.withRequiredEvents(SensoryEventWithIngredient.class, SensoryEventWithoutIngredient.class);

        assertEquals(interactionDescriptorWithRequiredEvents.requiredEvents().size(), 2);
        assertTrue(interactionDescriptorWithRequiredEvents.requiredEvents().contains(sensoryEventWithIngredientCheck()));
        assertTrue(interactionDescriptorWithRequiredEvents.requiredEvents().contains(sensoryEventWithoutIngredientCheck()));
    }

    @Test
    public void shouldUpdateTheRequiredOneOfEventList() {
        InteractionDescriptor interactionDescriptor = of(ProvidesIngredientInteraction.class);
        assertTrue(interactionDescriptor.requiredOneOfEvents().isEmpty());

        InteractionDescriptor interactionDescriptorWithRequiredOneOfEvents =
                interactionDescriptor.withRequiredOneOfEvents(SensoryEventWithIngredient.class, SensoryEventWithoutIngredient.class);

        assertEquals(interactionDescriptorWithRequiredOneOfEvents.requiredOneOfEvents().size(), 2);
        assertTrue(interactionDescriptorWithRequiredOneOfEvents.requiredOneOfEvents().contains(sensoryEventWithIngredientCheck()));
        assertTrue(interactionDescriptorWithRequiredOneOfEvents.requiredOneOfEvents().contains(sensoryEventWithoutIngredientCheck()));
    }

    //TODO add tests for all InteractionDescriptor methods
    //predefinedIngredients
    //overriddenIngredientNames
    //overriddenOutputIngredientName
    //maximumInteractionCount
    //failureStrategy
    //eventOutputTransformers
}
