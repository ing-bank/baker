package com.ing.baker;

import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.RecipeValidationException;
import com.ing.baker.core.BakerException;
import com.ing.baker.java_api.JBaker;
import com.ing.baker.recipe.javadsl.JRecipe;
import com.ing.baker.recipe.common.Interaction;
import com.typesafe.config.ConfigFactory;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.UUID;

import static com.ing.baker.JCompiledRecipeTest.setupComplexRecipe;
import static com.ing.baker.JCompiledRecipeTest.setupSimpleRecipe;
import static com.ing.baker.recipe.javadsl.JInteractionDescriptor.*;
import static org.junit.Assert.assertEquals;

public class JBakerTest {

    java.util.List<Interaction> implementationsList = ImmutableList.of(
            new JCompiledRecipeTest.InteractionOneImpl(),
            new JCompiledRecipeTest.InteractionTwo(),
            new JCompiledRecipeTest.InteractionThree());

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException {
        JBaker jBaker = new JBaker(JCompiledRecipeTest.setupSimpleRecipe(), implementationsList);
        assertEquals(jBaker.getCompiledRecipe().getValidationErrors().size(), 0);
        UUID requestId = UUID.randomUUID();
        jBaker.bake(requestId);
        jBaker.processEvent(requestId, new JCompiledRecipeTest.EventOne());
        assertEquals("{RequestIDStringOne=" + requestId.toString() + "}", jBaker.getIngredients(requestId).toString());
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException {
        com.typesafe.config.Config config = ConfigFactory.load();
        JBaker jBaker = new JBaker(JCompiledRecipeTest.setupSimpleRecipe(), implementationsList);
        assertEquals(jBaker.getCompiledRecipe().getValidationErrors().size(), 0);
        UUID requestId = UUID.randomUUID();
        jBaker.bake(requestId);
        jBaker.processEvent(requestId, new JCompiledRecipeTest.EventOne());
        assertEquals("{RequestIDStringOne=" + requestId.toString() + "}", jBaker.getIngredients(requestId).toString());
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException {
        exception.expect(RecipeValidationException.class);
        JBaker jBaker = new JBaker(JCompiledRecipeTest.setupComplexRecipe(), ImmutableList.<Interaction>of());
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException {
        JBaker jBaker = new JBaker(JCompiledRecipeTest.setupComplexRecipe(), implementationsList);
        UUID processId = UUID.randomUUID();
        jBaker.bake(processId);
        jBaker.processEvent(processId, new JCompiledRecipeTest.EventOne());
        jBaker.processEvent(processId, new JCompiledRecipeTest.EventTwo());
    }

    @Test
    public void shouldFailWhenSieveNotDefaultConstructor() throws BakerException {
        JRecipe recipe = JCompiledRecipeTest.setupComplexRecipe().withSieve(of(JCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));
        exception.expect(RecipeValidationException.class);
        JBaker jBaker = new JBaker(recipe, implementationsList);
    }
}
