package com.ing.baker;

import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.types.Converters;
import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.core.BakerException;
import com.ing.baker.runtime.java_api.JBaker;
import com.typesafe.config.ConfigFactory;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.UUID;
import java.util.concurrent.TimeoutException;

import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupComplexRecipe;
import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupSimpleRecipe;
import static org.junit.Assert.assertEquals;

public class JBakerTest {

    java.util.List<Object> implementationsList = ImmutableList.of(
            new JavaCompiledRecipeTest.InteractionOneImpl(),
            new JavaCompiledRecipeTest.InteractionTwo(),
            new JavaCompiledRecipeTest.InteractionThreeImpl(),
            new JavaCompiledRecipeTest.SieveImpl());


    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException, TimeoutException {

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(setupSimpleRecipe());
        String recipeName = compiledRecipe.name();

        JBaker jBaker = new JBaker();
        jBaker.addImplementations(implementationsList);
        String recipeId = jBaker.addRecipe(compiledRecipe);

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);
        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());

        assertEquals(1, jBaker.getIngredients(requestId).size());

        Object requestIdstringOne = jBaker.getIngredients(requestId).get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId.toString()), requestIdstringOne);
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException, TimeoutException {
        com.typesafe.config.Config config = ConfigFactory.load();

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(setupSimpleRecipe());
        String recipeName = compiledRecipe.name();

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);

        JBaker jBaker = new JBaker();
        jBaker.addImplementations(implementationsList);
        String recipeId =  jBaker.addRecipe(compiledRecipe);

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());

        assertEquals(1, jBaker.getIngredients(requestId).size());

        Object requestIdstringOne = jBaker.getIngredients(requestId).get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId.toString()), requestIdstringOne);
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException {

        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(setupComplexRecipe());
        JBaker jBaker = new JBaker();

        jBaker.addRecipe(compiledRecipe);
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException, TimeoutException {

        JBaker jBaker = new JBaker();

        jBaker.addImplementations(implementationsList);

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(setupComplexRecipe());

        String recipeId = jBaker.addRecipe(compiledRecipe);

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventTwo());
    }

    @Test
    public void shouldFailWhenSieveNotDefaultConstructor() throws BakerException {
        Recipe recipe = setupComplexRecipe().withSieve(InteractionDescriptor.of(JavaCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));

        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);

        JBaker jBaker = new JBaker();

        jBaker.addImplementations(implementationsList);

        jBaker.addRecipe(compiledRecipe);
    }
}
