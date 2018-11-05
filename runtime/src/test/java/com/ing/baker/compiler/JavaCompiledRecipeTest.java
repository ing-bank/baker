package com.ing.baker.compiler;

import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.ProcessId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.core.BakerException;
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

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compiledRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals("EventOne", recipe.getEvents().get(0).name());
        assertEquals("InteractionOne", recipe.getInteractions().get(0).name());

//        package$.MODULE$.dumpToFile("SimpleRecipe.svg", compiledRecipe.getVisualRecipeAsSVG());
    }

    @Test
    public void shouldCompileComplexRecipe() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compiledRecipe.getValidationErrors(), new ArrayList<String>());
        assertEquals("EventOne", recipe.getEvents().get(0).name());
        assertEquals("EventTwo", recipe.getEvents().get(1).name());

        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionOne")));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionTwo")));
        Assert.assertTrue(recipe.getInteractions().stream().anyMatch(a -> a.name().equals("InteractionThree")));

//        package$.MODULE$.dumpToFile("ComplexRecipe.svg", compiledRecipe.getVisualRecipeAsSVG());
    }

    @Test
    public void shouldCompileRecipeWithSieve() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compiledRecipe.getValidationErrors(), new ArrayList<String>());
        Assert.assertTrue(recipe.getSieves().stream().anyMatch(a -> a.name().equals("SieveImpl")));
    }

    @Test
    public void shouldShowVisualRecipe() throws BakerException {
        Recipe recipe = setupComplexRecipe();
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
        assertEquals(compiledRecipe.getValidationErrors().size(), 0);
        String visualRecipe = compiledRecipe.getRecipeVisualization();
        Assert.assertTrue("Should contain actionOne", visualRecipe.contains("actionOne"));
        Assert.assertTrue("Should contain actionTwo", visualRecipe.contains("actionTwo"));
        Assert.assertTrue("Should contain EventOne", visualRecipe.contains("EventOne"));
        Assert.assertTrue("Should contain EventTwo", visualRecipe.contains("EventTwo"));
        Assert.assertTrue("Should contain RequestIDStringOne", visualRecipe.contains("RequestIDStringOne"));

//        System.out.println(visualRecipe);
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

    public static class ProvideAppendRequestIds {
        public final String AppendedRequestIds;

        public ProvideAppendRequestIds(String appendedRequestIds) {
            AppendedRequestIds = appendedRequestIds;
        }
    }

    public static class SieveImpl {
        @FiresEvent(oneOf = {ProvideAppendRequestIds.class} )
        public ProvideAppendRequestIds apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                               @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return new ProvideAppendRequestIds(requestIDStringOne + requestIDStringTwo);
        }
    }

    public static class SieveImplWithoutDefaultConstruct {
        public SieveImplWithoutDefaultConstruct(String param){}

        @FiresEvent(oneOf = {ProvideAppendRequestIds.class} )
        public ProvideAppendRequestIds apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                            @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo) {
            return new ProvideAppendRequestIds(requestIDStringOne + requestIDStringTwo);
        }
    }

    public interface InteractionOne {

        class ProvidesRequestIDStringOne {
            public final String RequestIDStringOne;

            public ProvidesRequestIDStringOne(String requestIDStringOne) {
                this.RequestIDStringOne = requestIDStringOne;
            }
        }

        @FiresEvent(oneOf = { ProvidesRequestIDStringOne.class })
        ProvidesRequestIDStringOne apply(@ProcessId String requestId);
    }

    public static class InteractionOneImpl implements InteractionOne {
        public ProvidesRequestIDStringOne apply(String requestId) {
            return new ProvidesRequestIDStringOne(requestId);
        }

        public String name = "InteractionOne";
    }

    public static class InteractionTwo {

        class ProvidesRequestIDStringTwo {
            public final String RequestIDStringTwo;

            public ProvidesRequestIDStringTwo(String requestIDStringTwo) {
                this.RequestIDStringTwo = requestIDStringTwo;
            }
        }

        @FiresEvent(oneOf = {ProvidesRequestIDStringTwo.class})
        public ProvidesRequestIDStringTwo apply(@ProcessId String requestId) {
              return new ProvidesRequestIDStringTwo(requestId);
          }

        public String name = "InteractionTwo";
    }

    public interface InteractionThree {
        void apply(@RequiresIngredient("RequestIDStringOne") String requestIDStringOne,
                   @RequiresIngredient("RequestIDStringTwo") String requestIDStringTwo);
    }

    public static class InteractionThreeImpl implements InteractionThree {
        public void apply(String requestIDStringOne,
                          String requestIDStringTwo) {

        }

        public String name = InteractionThree.class.getSimpleName();
    }

    public static class RegisterIndividual {

        class ProvidesRequestIDStringThree {
            public final String RequestIDStringThree;

            public ProvidesRequestIDStringThree(String requestIDStringTwo) {
                this.RequestIDStringThree = requestIDStringTwo;
            }
        }

        @FiresEvent(oneOf = { ProvidesRequestIDStringThree.class })
        public ProvidesRequestIDStringThree apply(@ProcessId String requestId, @RequiresIngredient("RequestIDStringOne") String requestIDStringOne) {
            return new ProvidesRequestIDStringThree(requestId);
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
