package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.javadsl.interactions.ProvidesIngredientInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdStringInteraction;
import com.ing.baker.recipe.javadsl.interactions.RequiresProcessIdUUIDInteraction;
import org.junit.Test;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static com.ing.baker.recipe.javadsl.JavadslTestHelper.*;
import static org.junit.Assert.assertEquals;

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
        com.ing.baker.recipe.common.InteractionDescriptor interactionDescriptor = of(RequiresProcessIdUUIDInteraction.class);
        assertEquals(requiresProcessIdUUIDInteractionCheck(), interactionDescriptor.interaction());
    }

    //TODO add tests for all InteractionDescriptor methods
}
