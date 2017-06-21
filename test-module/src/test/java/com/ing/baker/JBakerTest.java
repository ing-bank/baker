package com.ing.baker;

import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.core.BakerException;
import com.ing.baker.runtime.java_api.JBaker;
import com.typesafe.config.ConfigFactory;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.UUID;

import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupComplexRecipe;
import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupSimpleRecipe;
import static org.junit.Assert.assertEquals;

//TODO move to runtime, not possbile now because it references parts of the RecipeCompilerSpec
public class JBakerTest {

    java.util.List<Object> implementationsList = ImmutableList.of(
            new JavaCompiledRecipeTest.InteractionOneImpl(),
            new JavaCompiledRecipeTest.InteractionTwo(),
            new JavaCompiledRecipeTest.InteractionThreeImpl(),
            new JavaCompiledRecipeTest.SieveImpl());

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException {
        JBaker jBaker = new JBaker(RecipeCompiler.compileRecipe(setupSimpleRecipe()), implementationsList);
        assertEquals(jBaker.getCompiledRecipe().getValidationErrors().size(), 0);
        UUID requestId = UUID.randomUUID();
        jBaker.bake(requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());
        assertEquals("{RequestIDStringOne=" + requestId.toString() + "}", jBaker.getIngredients(requestId).toString());
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException {
        com.typesafe.config.Config config = ConfigFactory.load();
        JBaker jBaker = new JBaker(RecipeCompiler.compileRecipe(setupSimpleRecipe()), implementationsList);
        assertEquals(jBaker.getCompiledRecipe().getValidationErrors().size(), 0);
        UUID requestId = UUID.randomUUID();
        jBaker.bake(requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());
        assertEquals("{RequestIDStringOne=" + requestId.toString() + "}", jBaker.getIngredients(requestId).toString());
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException {
        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(setupComplexRecipe());
        JBaker jBaker = new JBaker(compiledRecipe, ImmutableList.<Object>of());
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException {
        JBaker jBaker = new JBaker(RecipeCompiler.compileRecipe(setupComplexRecipe()), implementationsList);
        UUID processId = UUID.randomUUID();
        jBaker.bake(processId);
        jBaker.processEvent(processId, new JavaCompiledRecipeTest.EventOne());
        jBaker.processEvent(processId, new JavaCompiledRecipeTest.EventTwo());
    }

    @Test
    public void shouldFailWhenSieveNotDefaultConstructor() throws BakerException {
        Recipe recipe = setupComplexRecipe().withSieve(InteractionDescriptor.of(JavaCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));
        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);
        JBaker jBaker = new JBaker(compiledRecipe, implementationsList);
    }
}
