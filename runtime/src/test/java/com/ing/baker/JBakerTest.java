package com.ing.baker;

import akka.actor.ActorSystem;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.akka.ProcessState;
import com.ing.baker.runtime.akka.events.ProcessCreated;
import com.ing.baker.runtime.akka.events.Subscribe;
import com.ing.baker.runtime.common.BakerException;
import com.ing.baker.runtime.javadsl.JBaker;
import com.ing.baker.runtime.javadsl.SensoryEventResult;
import com.ing.baker.types.Converters;
import com.ing.baker.types.Value;
import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.UUID;
import java.util.concurrent.ExecutionException;

import static org.junit.Assert.assertEquals;

public class JBakerTest {

    private java.util.List<Object> implementationsList = ImmutableList.of(
            new JavaCompiledRecipeTest.InteractionOneImpl(),
            new JavaCompiledRecipeTest.InteractionTwo(),
            new JavaCompiledRecipeTest.InteractionThreeImpl(),
            new JavaCompiledRecipeTest.SieveImpl());

    private static ActorSystem actorSystem = null;
    private static Config config = null;


    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @BeforeClass
    public static void init() {
        config = ConfigFactory.load();
        actorSystem = ActorSystem.apply("JBakerTest");
    }

    @AfterClass
    public static void tearDown() {
        if (actorSystem != null) actorSystem.terminate();
    }

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException, ExecutionException, InterruptedException {

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        String processId = UUID.randomUUID().toString();
        JBaker jBaker = JBaker.akka(config, actorSystem);
        java.util.Map<String, Value> ingredients = jBaker.addImplementations(implementationsList)
            .thenCompose(x -> jBaker.addRecipe(compiledRecipe))
            .thenCompose(recipeId -> {
                assertEquals(compiledRecipe.getValidationErrors().size(), 0);
                return jBaker.bake(recipeId, processId);
            })
            .thenCompose(x -> jBaker.fireSensoryEventCompleted(processId, new JavaCompiledRecipeTest.EventOne()))
            .thenApply(SensoryEventResult::events)
            .thenCompose(x -> jBaker.getProcessState(processId))
            .thenApply(ProcessState::getIngredients)
            .get();

        assertEquals(1, ingredients.size());
        Object requestIdstringOne = ingredients.get("RequestIDStringOne");
        assertEquals(Converters.toValue(processId), requestIdstringOne);
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException, ExecutionException, InterruptedException {
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);

        JBaker jBaker = JBaker.akka(config, actorSystem);
        jBaker.addImplementations(implementationsList);
        String recipeId = jBaker.addRecipe(compiledRecipe).get();

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();
        jBaker.fireSensoryEventCompleted(requestId, new JavaCompiledRecipeTest.EventOne()).get();
        java.util.Map<String, Value> ingredients = jBaker.getProcessState(requestId).get().getIngredients();

        assertEquals(1, ingredients.size());

        Object requestIdstringOne = ingredients.get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId), requestIdstringOne);
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException, ExecutionException, InterruptedException {

        exception.expect(ExecutionException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());
        JBaker jBaker = JBaker.akka(config, actorSystem);

        jBaker.addRecipe(compiledRecipe).get();
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException, ExecutionException, InterruptedException {

        JBaker jBaker = JBaker.akka(config, actorSystem);

        jBaker.addImplementations(implementationsList);

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());

        String recipeId = jBaker.addRecipe(compiledRecipe).get();

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();
        jBaker.fireSensoryEventCompleted(requestId, new JavaCompiledRecipeTest.EventOne()).get();
        jBaker.fireSensoryEventCompleted(requestId, new JavaCompiledRecipeTest.EventTwo()).get();
    }

    final static class EmptySubscriber {
        @SuppressWarnings("unused")
        @Subscribe
        public void onEvent(ProcessCreated e) {
            // intentionally left empty
        }
    }

}
