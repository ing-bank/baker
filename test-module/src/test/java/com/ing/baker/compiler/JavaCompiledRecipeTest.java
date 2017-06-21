package com.ing.baker.compiler;

import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.runtime.core.BakerException;
import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.ProvidesIngredient;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.il.CompiledRecipe;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static org.junit.Assert.assertEquals;

public class JavaCompiledRecipeTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldCompileSimpleRecipe() throws BakerException {
        Recipe recipe = setupSimpleRecipe();

        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals("EventOne", recipe.getEvents().get(0).name());
        assertEquals("InteractionOne", recipe.getInteractions().get(0).name());
    }

    @Test
    public void shouldCompileComplexRecipe() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals("EventOne", recipe.getEvents().get(0).name());
        assertEquals("EventTwo", recipe.getEvents().get(1).name());

        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionOne")));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionTwo")));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionThree")));
    }


    @Test
    public void shouldCompileRecipeWithSieve() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compileRecipe.getValidationErrors(), new ArrayList<String>());
        Assert.assertTrue(recipe.getSieves().stream().anyMatch(a -> a.name().equals("SieveImpl")));
    }

    @Test
    public void shouldShowVisualRecipe() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getRecipeVisualization();
        Assert.assertTrue("Should contain actionOne", visualRecipe.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should contain EventOne", visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));

        System.out.println(compileRecipe.getRecipeVisualization());
    }

    @Test
    public void shouldShowPetriNetVisual() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
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
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
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
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compileRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compileRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compileRecipe.getFilteredRecipeVisualization(new String[]{"actionOne", "EventTwo"});
        Assert.assertTrue("Should not contain actionOne", !visualRecipe.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should not contain EventOne", !visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", !visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));
        Assert.assertTrue("Should contain RequestIDStringTwo", visualRecipe.contains("RequestIDStringTwo"));
    }

    public static class EventOne {}

    public static class EventTwo {}

    public static class EventWithoutIngredientsNorPreconditions{}

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

        public String name = "InteractionOne";
    }

    public static class InteractionTwo implements Interaction {
        @ProvidesIngredient("RequestIDStringTwo")
        public String apply(@ProcessId String requestId) {
              return requestId;
          }

        public String name = "InteractionTwo";
    }

    public interface InteractionThree extends Interaction {
        public void apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                          @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo);
    }

    public static class InteractionThreeImpl implements InteractionThree {
        public void apply(String requestIDStringOne,
                          String requestIDStringTwo) {

        }

        public String name = InteractionThree.class.getSimpleName();
    }

    public static class RegisterIndividual implements Interaction {

        @ProvidesIngredient("RequestIDStringThree")
        public String apply(@ProcessId String requestId, @RequiresIngredient("RequestIDStringOne") String requestIDStringOne) {
            return requestId;
        }
    }

    public static Recipe setupSimpleRecipe() {
        return new Recipe("TestRecipe")
                .withInteraction(of(InteractionOne.class)
                        .withRequiredEvent(EventOne.class))
                .withSensoryEvent(EventOne.class);
    }

    public static Recipe setupComplexRecipe() {
        return new Recipe("TestRecipe")
                .withInteractions(
                        of(InteractionOne.class)
                                .withRequiredEvent(EventOne.class),
                        of(InteractionOne.class, "InteractionOneRenamed")
                                .withRequiredEvent(EventOne.class),
                        of(InteractionTwo.class)
                                .withRequiredEvent(EventTwo.class),
                        of(InteractionThree.class))
                .withSensoryEvents(
                        EventOne.class,
                        EventTwo.class,
                        EventWithoutIngredientsNorPreconditions.class)
                .withSieve(
                        of(SieveImpl.class));
    }
}
