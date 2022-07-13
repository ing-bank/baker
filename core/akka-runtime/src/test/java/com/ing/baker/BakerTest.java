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
        java.util.Map<String, Value> ingredients = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false))
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
        String recipeId = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false)).get();

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

        jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), true)).get();
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
        String recipeId = jBaker.addRecipe(RecipeRecord.of(compiledRecipe, System.currentTimeMillis(), false)).get();
        EventInstance eventOne = EventInstance.from(new JavaCompiledRecipeTest.EventOne());
        assertEquals(eventOne.getName(), "EventOne");
        assertTrue(eventOne.getProvidedIngredients().isEmpty());

        // Bake and fire events
        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId).get();
        EventResolutions moments = jBaker.fireEvent(requestId, eventOne);
        assertEquals(moments.resolveWhenReceived().get(), SensoryEventStatus.Received);
        SensoryEventResult result = moments.resolveWhenCompleted().get();
        assertEquals(SensoryEventStatus.Completed, result.getSensoryEventStatus());
        assertEquals(3, result.getEventNames().size());
        assertEquals(1, result.getIngredients().size());
        assertTrue(result.getEventNames().contains("EventOne"));
        assertNotNull(result.ingredients().get("RequestIDStringOne"));

        // Enquiry State
        RecipeInstanceState state = jBaker.getRecipeInstanceState(requestId).get();
        assertEquals(state.getEventNames().get(0), "EventOne");
        assertEquals(state.getEvents().get(0).getName(), "EventOne");
        assertEquals(requestId, state.getRecipeInstanceId());
        assertEquals(state, state.asScala().asJava());
        assertTrue(state.getEvents().get(0).getOccurredOn() > 0);

        Set<RecipeInstanceMetadata> data = jBaker.getAllRecipeInstancesMetadata().get();
        assertEquals(data.size(), 1);
        RecipeInstanceMetadata instance1Data = data.iterator().next();
        assertTrue(instance1Data.getCreatedTime() > 1);
        assertEquals(instance1Data.getRecipeId(), recipeId);
        assertEquals(instance1Data.getRecipeInstanceId(), requestId);
        assertEquals(instance1Data, instance1Data.asScala().asJava());

        Map<String, RecipeInformation> recipes = jBaker.getAllRecipes().get();
        assertEquals(recipes.size(), 1);
        RecipeInformation recipe1 = recipes.get(recipeId);
        assertEquals(recipe1.getCompiledRecipe(), compiledRecipe);
        assertEquals(recipe1.getErrors().size(), 0);
        assertTrue(recipe1.getRecipeCreatedTime() > 0);
        assertEquals(recipe1.getRecipeId(), recipeId);

        EventResolutions res = jBaker.fireEvent(requestId, EventInstance.from(new JavaCompiledRecipeTest.EventTwo()));
        SensoryEventStatus status = res.getResolveWhenReceived().get();
        assertEquals(status, SensoryEventStatus.Received);
        res.getResolveWhenCompleted().get();

        bakerEvents.forEach(event -> {
            if (event instanceof RecipeAdded) {
                RecipeAdded event0 = (RecipeAdded) event;
                assertEquals(compiledRecipe, event0.compiledRecipe());
                assertTrue(event0.date() > 0);
                assertEquals(recipeId, event0.getRecipeId());
                assertEquals("TestRecipe", event0.recipeName());
                assertTrue(event0.getData() > 0);
            } else if (event instanceof RecipeInstanceCreated) {
                RecipeInstanceCreated event0 = (RecipeInstanceCreated) event;
                assertEquals(recipeId, event0.getRecipeId());
                assertEquals(requestId, event0.getRecipeInstanceId());
                assertEquals("TestRecipe", event0.getRecipeName());
                assertTrue(event0.getTimeStamp() > 0);
            } else if (event instanceof EventReceived) {
                EventReceived event0 = (EventReceived) event;
                assertEquals(recipeId, event0.getRecipeId());
                assertEquals(requestId, event0.getRecipeInstanceId());
                assertTrue(event0.getTimeStamp() > 0);
                String eventName = event0.getEvent().getName();
                assertTrue("EventOne".equals(eventName) || "EventTwo".equals(eventName));
                assertEquals(Optional.empty(), event0.getCorrelationId());
            } else if (event instanceof InteractionStarted) {
                InteractionStarted event0 = (InteractionStarted) event;
                assertEquals(recipeId, event0.getRecipeId());
                assertEquals(requestId, event0.getRecipeInstanceId());
                assertTrue(event0.getTimeStamp() > 0);
                assertEquals("TestRecipe", event0.getRecipeName());
                String eventName = event0.getInteractionName();
                assertTrue("InteractionOne".equals(eventName) ||
                       "InteractionOneRenamed".equals(eventName) ||
                       "InteractionTwo".equals(eventName) ||
                       "SieveImpl".equals(eventName) ||
                       "InteractionThree".equals(eventName));
            } else if (event instanceof InteractionCompleted) {
                InteractionCompleted event0 = (InteractionCompleted) event;
                assertEquals(recipeId, event0.getRecipeId());
                assertEquals(requestId, event0.getRecipeInstanceId());
                assertTrue(event0.getTimeStamp() > 0);
                assertEquals("TestRecipe", event0.getRecipeName());
                String interactionName = event0.getInteractionName();
                assertTrue("InteractionOne".equals(interactionName) ||
                        "InteractionOneRenamed".equals(interactionName) ||
                        "InteractionTwo".equals(interactionName) ||
                        "SieveImpl".equals(interactionName) ||
                        "InteractionThree".equals(interactionName));
            }
        });

        IngredientInstance ing = new IngredientInstance("ingredient", new PrimitiveValue("this"));
        assertEquals("ingredient", ing.getName());
        assertEquals("this", ing.getValue().as(String.class));
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
