package com.ing.baker;

import com.ing.baker.api.Event;
import com.ing.baker.core.*;
import com.ing.baker.core.InteractionDescriptor;
import com.ing.baker.java_api.*;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;

import static com.ing.baker.java_api.JInteractionDescriptor.of;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class JCompiledRecipeTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldCompileSimpleRecipe() throws BakerException {
        JRecipe recipe = setupSimpleRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals(JCompiledRecipeTest.EventOne.class, recipe.getEvents().get(0));
        assertEquals(InteractionOne.class, recipe.getInteractions().get(0).interactionClass());
    }

    @Test
    public void shouldCompileComplexRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals(JCompiledRecipeTest.EventOne.class, recipe.getEvents().get(0));
        assertEquals(JCompiledRecipeTest.EventTwo.class, recipe.getEvents().get(1));

        assertTrue(recipe.getInteractions().stream().anyMatch((com.ing.baker.core.InteractionDescriptor a) -> a.interactionClass() == InteractionOne.class));
        assertTrue(recipe.getInteractions().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == InteractionTwo.class));
        assertTrue(recipe.getInteractions().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == InteractionThree.class));
    }


    @Test
    public void shouldCompileRecipeWithSieve() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertTrue(recipe.getSieves().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == SieveImpl.class));
    }

    @Test
    public void shouldCompileRecipeWithSieveWithoutDefaultConstructorWithErrors() throws BakerException {
        JRecipe recipe = setupComplexRecipe().withSieve(of(JCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors().size(), 1);
    }

    @Test
    public void shouldShowVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getRecipeVisualization();
        assertTrue("Should contain actionOne", visualRecipe.contains("actionOne"));
        assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        assertTrue("Should contain EventOne", visualRecipe.contains("EventOne"));
        assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
    }

    @Test
    public void shouldShowPetriNetVisual() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String petrinetVisual = compileRecipe.getPetriNetVisualization();
        assertTrue("Should contain actionOne", petrinetVisual.contains("actionOne"));
        assertTrue("Should contain actionTwo", petrinetVisual.contains("actionTwo"));
        assertTrue("Should contain EventOne", petrinetVisual.contains("EventOne"));
        assertTrue("Should contain EventTwo", petrinetVisual.contains("EventTwo"));
        assertTrue("Should contain RequestIDStringOne", petrinetVisual.contains("RequestIDStringOne"));
    }

    @Test
    public void shouldShowFilteredVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getFilteredRecipeVisualization("InteractionOne");
        assertTrue("Should not contain actionOne", !visualRecipe.contains("InteractionOne"));
        assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        assertTrue("Should not contain EventOne", !visualRecipe.contains("EventOne"));
        assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
        assertTrue("Should contain RequestIDStringTwo", visualRecipe.contains("RequestIDStringTwo"));
    }

    @Test
    public void shouldShowFilteredMultipleVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = recipe.compileRecipe();
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getFilteredRecipeVisualization(new String[]{"actionOne", "EventTwo"});
        assertTrue("Should not contain actionOne", !visualRecipe.contains("actionOne"));
        assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        assertTrue("Should not contain EventOne", !visualRecipe.contains("EventOne"));
        assertTrue("Should contain EventTwo", !visualRecipe.contains("EventTwo"));
        assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
        assertTrue("Should contain RequestIDStringTwo", visualRecipe.contains("RequestIDStringTwo"));
    }

    static class EventOne implements Event {
    }

    static class EventTwo implements Event {
    }

    static class EventWithoutIngredientsNorPreconditions implements Event {
    }

    public static class SieveImpl implements JInteraction {
        @ProvidesIngredient("AppendedRequestIds")
        public String apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                               @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return requestIDStringOne + requestIDStringTwo;
        }
    }

    public static class SieveImplWithoutDefaultConstruct implements JInteraction {
        public SieveImplWithoutDefaultConstruct(String param){}

        @ProvidesIngredient("AppendedRequestIds")
        public String apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                            @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return requestIDStringOne + requestIDStringTwo;
        }
    }

    public interface InteractionOne extends JInteraction {
        @ProvidesIngredient("RequestIDStringOne")
        public String apply(@ProcessId String requestId);
    }

    public static class InteractionOneImpl implements InteractionOne {
        public String apply(String requestId) {
            return requestId;
        }
    }

    public static class InteractionTwo implements JInteraction {
        @ProvidesIngredient("RequestIDStringTwo")
        public String apply(@ProcessId String requestId) {
              return requestId;
          }
    }

    public static class InteractionThree implements JInteraction {
        public void apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                          @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {

        }
    }

    public static class RegisterIndividual implements JInteraction {

        @ProvidesIngredient("RequestIDStringThree")
        public String apply(@ProcessId String requestId, @RequiresIngredient("RequestIDStringOne") String requestIDStringOne) {
            return requestId;
        }
    }

    static JRecipe setupSimpleRecipe() {
        return new JRecipe("TestRecipe")
                .withInteraction(of(InteractionOne.class).withRequiredEvent(EventOne.class))
                .withSensoryEvent(EventOne.class);
    }

    static JRecipe setupComplexRecipe() {
        return new JRecipe("TestRecipe")
                .withInteractions(
                        of(InteractionOne.class)
                                .withRequiredEvent(EventOne.class),
                        of(InteractionOne.class, "InteractionOneRenamed")
                                .withRequiredEvent(EventOne.class),
                        of(InteractionTwo.class).withRequiredEvent(EventTwo.class),
                        of(InteractionThree.class))
                .withSensoryEvents(
                        EventOne.class,
                        EventTwo.class,
                        EventWithoutIngredientsNorPreconditions.class)
                .withSieve(of(SieveImpl.class));
    }
}
