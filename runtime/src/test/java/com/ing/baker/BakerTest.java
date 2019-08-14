package com.ing.baker;

import akka.actor.ActorSystem;
import akka.stream.ActorMaterializer;
import akka.stream.Materializer;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.javadsl.*;
import com.ing.baker.runtime.common.BakerException;
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

public class BakerTest {

    private java.util.List<InteractionInstance> implementationsList = ImmutableList.of(
            InteractionInstance.from(new JavaCompiledRecipeTest.InteractionOneImpl()),
            InteractionInstance.from(new JavaCompiledRecipeTest.InteractionTwo()),
            InteractionInstance.from(new JavaCompiledRecipeTest.InteractionThreeImpl()),
            InteractionInstance.from(new JavaCompiledRecipeTest.SieveImpl()));

    private static ActorSystem actorSystem = null;
    private static Materializer materializer = null;
    private static Config config = null;


    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @BeforeClass
    public static void init() {
        config = ConfigFactory.load();
        actorSystem = ActorSystem.apply("JBakerTest");
        materializer = ActorMaterializer.create(actorSystem);
    }

    @AfterClass
    public static void tearDown() {
        if (actorSystem != null) actorSystem.terminate();
    }

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException, ExecutionException, InterruptedException {

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        String recipeInstanceId = UUID.randomUUID().toString();
        Baker jBaker = Baker.akka(config, actorSystem, materializer);
        java.util.Map<String, Value> ingredients = jBaker.addInteractionInstance(implementationsList)
                .thenCompose(x -> jBaker.addRecipe(compiledRecipe))
                .thenCompose(recipeId -> {
                    assertEquals(compiledRecipe.getValidationErrors().size(), 0);
                    return jBaker.bake(recipeId, recipeInstanceId);
                })
                .thenCompose(x -> jBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.from(new JavaCompiledRecipeTest.EventOne())))
                .thenApply(EventResult::events)
                .thenCompose(x -> jBaker.getRecipeInstanceState(recipeInstanceId))
                .thenApply(RecipeInstanceState::getIngredients)
                .get();

        assertEquals(1, ingredients.size());
        Object requestIdstringOne = ingredients.get("RequestIDStringOne");
        assertEquals(Converters.toValue(recipeInstanceId), requestIdstringOne);
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException, ExecutionException, InterruptedException {
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);

        Baker jBaker = Baker.akka(config, actorSystem, materializer);
        jBaker.addInteractionInstance(implementationsList);
        String recipeId = jBaker.addRecipe(compiledRecipe).get();

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();
        jBaker.fireEventAndResolveWhenCompleted(requestId, EventInstance.from(new JavaCompiledRecipeTest.EventOne())).get();
        java.util.Map<String, Value> ingredients = jBaker.getRecipeInstanceState(requestId).get().getIngredients();

        assertEquals(1, ingredients.size());

        Object requestIdstringOne = ingredients.get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId), requestIdstringOne);
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException, ExecutionException, InterruptedException {

        exception.expect(ExecutionException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());
        Baker jBaker = Baker.akka(config, actorSystem, materializer);

        jBaker.addRecipe(compiledRecipe).get();
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException, ExecutionException, InterruptedException {

        Baker jBaker = Baker.akka(config, actorSystem, materializer);

        jBaker.addInteractionInstance(implementationsList);

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());

        String recipeId = jBaker.addRecipe(compiledRecipe).get();

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();
        jBaker.fireEventAndResolveWhenCompleted(requestId, EventInstance.from(new JavaCompiledRecipeTest.EventOne())).get();
        jBaker.fireEventAndResolveWhenCompleted(requestId, EventInstance.from(new JavaCompiledRecipeTest.EventTwo())).get();
    }
}
