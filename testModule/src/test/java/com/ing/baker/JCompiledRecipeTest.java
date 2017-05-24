package com.ing.baker;

import com.ing.baker.compiledRecipe.annotations.ProcessId;
import com.ing.baker.compiledRecipe.annotations.ProvidesIngredient;
import com.ing.baker.compiledRecipe.annotations.RequiresIngredient;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.core.BakerException;
import com.ing.baker.recipe.common.Event;
import com.ing.baker.recipe.common.Interaction;
import com.ing.baker.recipe.common.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.JRecipe;
import com.ing.baker.runtime.java_api.JCompiledRecipe;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;

import static com.ing.baker.recipe.javadsl.JInteractionDescriptor.of;
import static org.junit.Assert.assertEquals;

public class JCompiledRecipeTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldCompileSimpleRecipe() throws BakerException {
        JRecipe recipe = setupSimpleRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals(JCompiledRecipeTest.EventOne.class, recipe.getEvents().get(0));
        assertEquals(InteractionOne.class, recipe.getInteractions().get(0).interactionClass());
    }

    @Test
    public void shouldCompileComplexRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals(JCompiledRecipeTest.EventOne.class, recipe.getEvents().get(0));
        assertEquals(JCompiledRecipeTest.EventTwo.class, recipe.getEvents().get(1));

        Assert.assertTrue(recipe.getInteractions().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == InteractionOne.class));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == InteractionTwo.class));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == InteractionThree.class));
    }


    @Test
    public void shouldCompileRecipeWithSieve() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        Assert.assertTrue(recipe.getSieves().stream().anyMatch((InteractionDescriptor a) -> a.interactionClass() == SieveImpl.class));
    }

    @Test
    public void shouldCompileRecipeWithSieveWithoutDefaultConstructorWithErrors() throws BakerException {
        JRecipe recipe = setupComplexRecipe().withSieve(of(JCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors().size(), 1);
    }

    @Test
    public void shouldShowVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getRecipeVisualization();
        Assert.assertTrue("Should contain actionOne", visualRecipe.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should contain EventOne", visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
    }

    @Test
    public void shouldShowPetriNetVisual() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String petrinetVisual = compileRecipe.getPetriNetVisualization();
        Assert.assertTrue("Should contain actionOne", petrinetVisual.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", petrinetVisual.contains("actionTwo"));
        Assert.assertTrue("Should contain EventOne", petrinetVisual.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", petrinetVisual.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", petrinetVisual.contains("RequestIDStringOne"));
    }

    @Test
    public void shouldShowFilteredVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getFilteredRecipeVisualization("InteractionOne");
        Assert.assertTrue("Should not contain actionOne", !visualRecipe.contains("InteractionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should not contain EventOne", !visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
        Assert.assertTrue("Should contain RequestIDStringTwo", visualRecipe.contains("RequestIDStringTwo"));
    }

    @Test
    public void shouldShowFilteredMultipleVisualRecipe() throws BakerException {
        JRecipe recipe = setupComplexRecipe();
        JCompiledRecipe compileRecipe = new JCompiledRecipe(RecipeCompiler.compileRecipe(recipe));
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getFilteredRecipeVisualization(new String[]{"actionOne", "EventTwo"});
        Assert.assertTrue("Should not contain actionOne", !visualRecipe.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should not contain EventOne", !visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", !visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
        Assert.assertTrue("Should contain RequestIDStringTwo", visualRecipe.contains("RequestIDStringTwo"));
    }

    public static class EventOne implements Event {
    }

    public static class EventTwo implements Event {
    }

    public static class EventWithoutIngredientsNorPreconditions implements Event {
    }

    public static class SieveImpl implements Interaction {
        @ProvidesIngredient("AppendedRequestIds")
        public String apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                               @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return requestIDStringOne + requestIDStringTwo;
        }
    }

    public static class SieveImplWithoutDefaultConstruct implements Interaction {
        public SieveImplWithoutDefaultConstruct(String param){}

        @ProvidesIngredient("AppendedRequestIds")
        public String apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                            @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return requestIDStringOne + requestIDStringTwo;
        }
    }

    public interface InteractionOne extends Interaction {
        @ProvidesIngredient("RequestIDStringOne")
        String apply(@ProcessId String requestId);
    }

    public static class InteractionOneImpl implements InteractionOne {
        public String apply(String requestId) {
            return requestId;
        }
    }

    public static class InteractionTwo implements Interaction {
        @ProvidesIngredient("RequestIDStringTwo")
        public String apply(@ProcessId String requestId) {
              return requestId;
          }
    }

    public static class InteractionThree implements Interaction {
        public void apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                          @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {

        }
    }

    public static class RegisterIndividual implements Interaction {

        @ProvidesIngredient("RequestIDStringThree")
        public String apply(@ProcessId String requestId, @RequiresIngredient("RequestIDStringOne") String requestIDStringOne) {
            return requestId;
        }
    }

    public static JRecipe setupSimpleRecipe() {
        return new JRecipe("TestRecipe")
                .withInteraction(of(InteractionOne.class).withRequiredEvent(EventOne.class))
                .withSensoryEvent(EventOne.class);
    }

    public static JRecipe setupComplexRecipe() {
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
