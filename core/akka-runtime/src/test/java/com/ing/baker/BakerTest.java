package com.ing.baker;

import akka.actor.ActorSystem;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.runtime.akka.AkkaBaker;
import com.ing.baker.runtime.common.BakerException;
import com.ing.baker.runtime.common.InteractionExecutionFailureReason;
import com.ing.baker.runtime.common.RecipeRecord;
import com.ing.baker.runtime.common.SensoryEventStatus;
import com.ing.baker.runtime.javadsl.*;
import com.ing.baker.types.Converters;
import com.ing.baker.types.PrimitiveValue;
import com.ing.baker.types.Value;
import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.*;
import java.util.concurrent.ExecutionException;

import static org.junit.Assert.*;

public class BakerTest {

    private InteractionInstance interactionOneInstance = InteractionInstance.from(new JavaCompiledRecipeTest.InteractionOneImpl());
    private java.util.List<Object> implementationsList = ImmutableList.of(
            interactionOneInstance,
            InteractionInstance.from(new JavaCompiledRecipeTest.InteractionTwo()),
            InteractionInstance.from(new JavaCompiledRecipeTest.InteractionThreeImpl()),
            InteractionInstance.from(new JavaCompiledRecipeTest.SieveImpl()));

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

        String recipeInstanceId = UUID.randomUUID().toString();
        Baker jBaker = AkkaBaker.java(config, actorSystem, implementationsList);
        java.util.Map<String, Value> ingredients = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false, true))
                .thenCompose(recipeId -> {
                    assertEquals(compiledRecipe.getValidationErrors().size(), 0);
                    return jBaker.bake(recipeId, recipeInstanceId);
                })
                .thenCompose(x -> jBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.from(new JavaCompiledRecipeTest.EventOne())))
                .thenApply(SensoryEventResult::eventNames)
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

        Baker jBaker = AkkaBaker.java(config, actorSystem, implementationsList);
        String recipeId = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false, true)).get();

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
        Baker jBaker = AkkaBaker.java(config, actorSystem);

        jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), true, true)).get();
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException, ExecutionException, InterruptedException {
        actorSystem.terminate();
        actorSystem = ActorSystem.apply("shouldExecuteCompleteFlow");

        Baker jBaker = AkkaBaker.java(config, actorSystem, implementationsList);

        List<BakerEvent> bakerEvents = new LinkedList<>();
        jBaker.registerBakerEventListener(bakerEvents::add);

        // Setup recipe
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());
        String recipeId = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false, true)).get();
        EventInstance eventOne = EventInstance.from(new JavaCompiledRecipeTest.EventOne());
        assertEquals(eventOne.getName(), "EventOne");
        assertTrue(eventOne.getProvidedIngredients().isEmpty());

        // Bake and fire events
        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();

        jBaker.fireSensoryEventAndAwaitReceived(requestId, eventOne, "").get();
        jBaker.awaitEvent(requestId, "ProvidesRequestIDStringOne").get();
        jBaker.awaitIdle(requestId).get();

        var eventNames = jBaker.getEventNames(requestId).get();

        System.out.println(eventNames);
    }

    @Test
    public void testExecuteSingleInteractionSuccess() throws BakerException, ExecutionException, InterruptedException {
        Baker jBaker = AkkaBaker.java(config, actorSystem, implementationsList);
        List<IngredientInstance> ingredients = new ArrayList<>();
        ingredients.add(new IngredientInstance("requestId", new PrimitiveValue("requestId")));

        InteractionExecutionResult result = jBaker.executeSingleInteraction(interactionOneInstance.asScala().shaBase64(), ingredients).get();
        Map<String, Value> expectedIngredients = Map.of("RequestIDStringOne", new PrimitiveValue("requestId"));
        EventInstance expectedEventInstance = new EventInstance("ProvidesRequestIDStringOne", expectedIngredients);
        InteractionExecutionResult.Success expectedSuccess = new InteractionExecutionResult.Success(Optional.of(expectedEventInstance));
        assertEquals(result, new InteractionExecutionResult(
                Optional.of(expectedSuccess),
                Optional.empty()));
    }

    @Test
    public void testExecuteSingleInteractionNotFound() throws BakerException, ExecutionException, InterruptedException {
        Baker jBaker = AkkaBaker.java(config, actorSystem);

        InteractionExecutionResult result = jBaker.executeSingleInteraction("doesnotexist", Collections.emptyList()).get();
        assertEquals(result, new InteractionExecutionResult(
                Optional.empty(),
                Optional.of(new InteractionExecutionResult.Failure(InteractionExecutionFailureReason.INTERACTION_NOT_FOUND, Optional.empty(), Optional.empty()))));
    }

    @Test
    public void testExecuteSingleInteractionThatFails() throws BakerException, ExecutionException, InterruptedException {
        InteractionInstance interactionThatThrows = InteractionInstance.from(new JavaCompiledRecipeTest.InteractionThatThrowsImpl());
        Baker jBaker = AkkaBaker.java(config, actorSystem, List.of(interactionThatThrows));
        List<IngredientInstance> ingredients = new ArrayList<>();
        ingredients.add(new IngredientInstance("requestId", new PrimitiveValue("requestId")));

        InteractionExecutionResult result = jBaker.executeSingleInteraction(interactionThatThrows.asScala().shaBase64(), ingredients).get();
        assertEquals(result, new InteractionExecutionResult(
                Optional.empty(),
                Optional.of(new InteractionExecutionResult.Failure(InteractionExecutionFailureReason.INTERACTION_EXECUTION_ERROR,
                        Optional.of("InteractionThatThrowsImpl"), Optional.of("Interaction execution failed. Interaction threw InvocationTargetException with message null.")))));
    }
}
