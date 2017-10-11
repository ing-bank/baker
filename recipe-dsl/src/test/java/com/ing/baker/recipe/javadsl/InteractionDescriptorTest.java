package com.ing.baker.recipe.javadsl;

import com.ing.baker.recipe.common.RecipeValidationException;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent;
import com.ing.baker.recipe.javadsl.events.InteractionProvidedEvent2;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithIngredient;
import com.ing.baker.recipe.javadsl.events.SensoryEventWithoutIngredient;
import com.ing.baker.recipe.javadsl.interactions.*;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static com.ing.baker.recipe.javadsl.JavadslTestHelper.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

public class InteractionDescriptorTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldCreateInteractionDescriptorOfProvidesIngredientInteraction() {
        com.ing.baker.recipe.common.InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertEquals(providesIngredientInteractionCheck(), id.interaction());
    }

    @Test
    public void shouldCreateInteractionDescriptorOfRequiredProcessIdStringInteraction() {
        com.ing.baker.recipe.common.InteractionDescriptor id = of(RequiresProcessIdStringInteraction.class);
        assertEquals(requiresProcessIdStringInteractionCheck(), id.interaction());
    }

    @Test
    public void shouldNotAllowToCreateInteractionDescriptorWithProvidesIngredientAndFiresEvent() {
        exception.expect(RecipeValidationException.class);
        of(ProvidesIngredientAndFireseventInteraction.class);
    }

    @Test
    public void shouldCreateInteractionDescriptorWithDefaultName() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertEquals("ProvidesIngredientInteraction", id.name());
    }

    @Test
    public void shouldCreateInteractionDescriptorWithChangedName() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class, "ChangedName");
        assertEquals("ChangedName", id.name());
    }

    @Test
    public void shouldUpdateTheRequiredEventList() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.requiredEvents().isEmpty());

        InteractionDescriptor idWithRequiredEvent =
                id.withRequiredEvent(SensoryEventWithIngredient.class);

        assertEquals(idWithRequiredEvent.requiredEvents().size(), 1);
        assertTrue(idWithRequiredEvent.requiredEvents().contains(sensoryEventWithIngredientCheck().name()));

        InteractionDescriptor idWithRequiredEvents =
                id.withRequiredEvents(SensoryEventWithIngredient.class, SensoryEventWithoutIngredient.class);

        assertEquals(idWithRequiredEvents.requiredEvents().size(), 2);
        assertTrue(idWithRequiredEvents.requiredEvents().contains(sensoryEventWithIngredientCheck().name()));
        assertTrue(idWithRequiredEvents.requiredEvents().contains(sensoryEventWithoutIngredientCheck().name()));
    }

    @Test
    public void shouldUpdateTheRequiredOneOfEventList() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.requiredOneOfEvents().isEmpty());

        InteractionDescriptor idWithRequiredOneOfEvents =
                id.withRequiredOneOfEvents(SensoryEventWithIngredient.class, SensoryEventWithoutIngredient.class);

        assertEquals(idWithRequiredOneOfEvents.requiredOneOfEvents().size(), 2);
        assertTrue(idWithRequiredOneOfEvents.requiredOneOfEvents().contains(sensoryEventWithIngredientCheck().name()));
        assertTrue(idWithRequiredOneOfEvents.requiredOneOfEvents().contains(sensoryEventWithoutIngredientCheck().name()));
    }

    @Test(expected = IllegalArgumentException.class)
    public void shouldRejectUsingLessThanTwoOneOfRequiredEvents() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.requiredOneOfEvents().isEmpty());

        id.withRequiredOneOfEvents(SensoryEventWithIngredient.class);
    }

    @Test
    public void shouldUpdateTheMaximumInteractionCount() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.maximumInteractionCount().isEmpty());

        InteractionDescriptor idWithMaximumInteractionCount =
                id.withMaximumInteractionCount(1);
        assertTrue(idWithMaximumInteractionCount.maximumInteractionCount().isDefined());
        assertEquals(idWithMaximumInteractionCount.maximumInteractionCount().get(), 1);

        idWithMaximumInteractionCount =
                idWithMaximumInteractionCount.withMaximumInteractionCount(2);
        assertTrue(idWithMaximumInteractionCount.maximumInteractionCount().isDefined());
        assertEquals(idWithMaximumInteractionCount.maximumInteractionCount().get(), 2);
    }

    @Test
    public void shouldUpdateTheOverriddenOutputIngredientName() {
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.overriddenOutputIngredientName().isEmpty());

        InteractionDescriptor idWithOverriddenOutputIngredientName =
                id.renameProvidedIngredient("Renamed");

        assertTrue(idWithOverriddenOutputIngredientName.overriddenOutputIngredientName().isDefined());
        assertEquals(idWithOverriddenOutputIngredientName.overriddenOutputIngredientName().get(), "Renamed");
    }

    @Test
    public void shouldUpdateTheEventOutputTransformers(){
        InteractionDescriptor id = of(FiresEventInteraction.class);
        assertTrue(id.eventOutputTransformers().isEmpty());

        InteractionDescriptor idWithOutputEventTransformer =
                id.withEventTransformation(InteractionProvidedEvent.class, "transformedEventName");

        assertFalse(idWithOutputEventTransformer.eventOutputTransformers().isEmpty());
    }

    @Test
    public void shouldNotUpdateTheEventOutputTransformersWhenNotFiringEvent(){
        InteractionDescriptor id = of(ProvidesIngredientInteraction.class);
        assertTrue(id.eventOutputTransformers().isEmpty());

        exception.expect(RecipeValidationException.class);
        exception.expectMessage("Event transformation given for Interaction ProvidesIngredientInteraction but does not fire any event");
        InteractionDescriptor idWithOutputEventTransformer =
                id.withEventTransformation(InteractionProvidedEvent.class, "transformedEventName");

        assertTrue(idWithOutputEventTransformer.eventOutputTransformers().isEmpty());
    }

    @Test
    public void shouldNotUpdateTheEventOutputTransformersWhenSpecificEventNotFired(){
        InteractionDescriptor id = of(FiresEventInteraction.class);
        assertTrue(id.eventOutputTransformers().isEmpty());

        exception.expect(RecipeValidationException.class);
        exception.expectMessage("Event transformation given for Interaction FiresEventInteraction but does not fire event Event(InteractionProvidedEvent2)");
        InteractionDescriptor idWithOutputEventTransformer =
                id.withEventTransformation(InteractionProvidedEvent2.class, "transformedEventName");

        assertTrue(idWithOutputEventTransformer.eventOutputTransformers().isEmpty());
    }

    //TODO add tests for all InteractionDescriptor methods
    //predefinedIngredients
    //overriddenIngredientNames
    //failureStrategy
    //eventOutputTransformers
}
