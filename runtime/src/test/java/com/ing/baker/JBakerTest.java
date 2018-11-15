package com.ing.baker;

import akka.actor.ActorSystem;
import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.core.Baker;
import com.ing.baker.runtime.core.BakerException;
import com.ing.baker.runtime.core.EventListener;
import com.ing.baker.runtime.core.RecipeInformation;
import com.ing.baker.runtime.core.events.ProcessCreated;
import com.ing.baker.runtime.core.events.Subscribe;
import com.ing.baker.runtime.core.events.AnnotatedEventSubscriber;
import com.ing.baker.runtime.java_api.JBaker;
import com.ing.baker.types.Converters;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import scala.Option;
import scala.collection.immutable.List$;
import scala.concurrent.duration.FiniteDuration;

import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.*;

public class JBakerTest {

    private java.util.List<Object> implementationsList = ImmutableList.of(
            new JavaCompiledRecipeTest.InteractionOneImpl(),
            new JavaCompiledRecipeTest.InteractionTwo(),
            new JavaCompiledRecipeTest.InteractionThreeImpl(),
            new JavaCompiledRecipeTest.SieveImpl());

    private static ActorSystem actorSystem = null;

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @BeforeClass
    public static void init() {
        actorSystem = ActorSystem.apply("JBakerTest");
    }

    @AfterClass
    public static void tearDown() {
        if (actorSystem != null) actorSystem.terminate();
    }

    @Test
    public void shouldSetupJBakerWithDefaultActorFramework() throws BakerException, TimeoutException {

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        JBaker jBaker = new JBaker(actorSystem);
        jBaker.addImplementations(implementationsList);
        String recipeId = jBaker.addRecipe(compiledRecipe);

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);
        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());

        assertEquals(1, jBaker.getIngredients(requestId).size());

        Object requestIdstringOne = jBaker.getIngredients(requestId).get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId), requestIdstringOne);
    }

    @Test
    public void shouldSetupJBakerWithGivenActorFramework() throws BakerException, TimeoutException {
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupSimpleRecipe());

        assertEquals(compiledRecipe.getValidationErrors().size(), 0);

        JBaker jBaker = new JBaker(actorSystem);
        jBaker.addImplementations(implementationsList);
        String recipeId = jBaker.addRecipe(compiledRecipe);

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());

        assertEquals(1, jBaker.getIngredients(requestId).size());

        Object requestIdstringOne = jBaker.getIngredients(requestId).get("RequestIDStringOne");
        assertEquals(Converters.toValue(requestId), requestIdstringOne);
    }

    @Test
    public void shouldFailWhenMissingImplementations() throws BakerException {

        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());
        JBaker jBaker = new JBaker(actorSystem);

        jBaker.addRecipe(compiledRecipe);
    }

    @Test
    public void shouldProxyToBaker() throws Exception {

        Baker mockBaker = mock(Baker.class);

        JBaker jBaker = new JBaker(mockBaker, Collections.emptyList());

        String testRecipeId = "testRecipe";
        UUID processUUID = UUID.randomUUID();
        String processStringId = UUID.randomUUID().toString();
        String testEvent = "testEvent";
        String testCorrelationId = "testCorrelationId";
        java.time.Duration testTimeout = java.time.Duration.ofSeconds(1);
        FiniteDuration testTimeoutScala = new FiniteDuration(testTimeout.toMillis(), TimeUnit.MILLISECONDS);
        EventListener testListener = (processId, event) -> {
        };

        when(mockBaker.eventNames(any(String.class), any(FiniteDuration.class))).thenReturn(List$.MODULE$.empty());

        // -- register

        jBaker.registerBakerEventListener(new EmptySubscriber());
        verify(mockBaker).registerEventListenerPF(any(AnnotatedEventSubscriber.class));

        // -- bake

        jBaker.bake(testRecipeId, processStringId);
        verify(mockBaker).bake(eq(testRecipeId), eq(processStringId), any(FiniteDuration.class));

        jBaker.bake(testRecipeId, processUUID);
        verify(mockBaker).bake(eq(testRecipeId), eq(processUUID.toString()), any(FiniteDuration.class));

        // -- get ingredients

        jBaker.getIngredients(processStringId);
        verify(mockBaker).getIngredients(eq(processStringId), any(FiniteDuration.class));

        jBaker.getIngredients(processUUID);
        verify(mockBaker).getIngredients(eq(processUUID.toString()), any(FiniteDuration.class));

        // -- get events

        jBaker.getEvents(processStringId);
        verify(mockBaker).events(eq(processStringId), any(FiniteDuration.class));

        jBaker.getEvents(processUUID);
        verify(mockBaker).events(eq(processUUID.toString()), any(FiniteDuration.class));

        // -- get event names

        jBaker.getEventNames(processStringId);
        verify(mockBaker).eventNames(eq(processStringId), any(FiniteDuration.class));

        jBaker.getEventNames(processUUID);
        verify(mockBaker).eventNames(eq(processUUID.toString()), any(FiniteDuration.class));

        jBaker.getEventNames(processStringId, testTimeout);
        verify(mockBaker).eventNames(eq(processStringId), eq(testTimeoutScala));

        jBaker.getEventNames(processUUID, testTimeout);
        verify(mockBaker).eventNames(eq(processUUID.toString()), eq(testTimeoutScala));

        // -- get recipe

        when(mockBaker.getAllRecipes(any(FiniteDuration.class)))
                .thenReturn(new scala.collection.immutable.HashMap<String, RecipeInformation>());
        jBaker.getAllRecipes();
        verify(mockBaker).getAllRecipes(any(FiniteDuration.class));

        when(mockBaker.getRecipe(any(String.class), any(FiniteDuration.class)))
                .thenReturn(new RecipeInformation(null, 0l, new scala.collection.immutable.HashSet<String>()));
        jBaker.getRecipe(testRecipeId);
        verify(mockBaker).getRecipe(eq(testRecipeId), any(FiniteDuration.class));

        // -- get index

        jBaker.getIndex();
        verify(mockBaker).getIndex(any(FiniteDuration.class));

        jBaker.getIndex(testTimeout);
        verify(mockBaker).getIndex(eq(testTimeoutScala));

        // -- register listener

        jBaker.registerEventListener(testListener);
        verify(mockBaker).registerEventListener(eq(testListener));

        jBaker.registerEventListener(testRecipeId, testListener);
        verify(mockBaker).registerEventListener(eq(testRecipeId), eq(testListener));

        // -- process event

        jBaker.processEvent(processStringId, testEvent);
        verify(mockBaker).processEvent(eq(processStringId), eq(testEvent), eq(Option.empty()), any(FiniteDuration.class));

        jBaker.processEvent(processUUID, testEvent);
        verify(mockBaker).processEvent(eq(processUUID.toString()), eq(testEvent), eq(Option.empty()), any(FiniteDuration.class));

        // with correlation id

        jBaker.processEvent(processStringId, testEvent, testCorrelationId);
        verify(mockBaker).processEvent(eq(processStringId), eq(testEvent), eq(Option.apply(testCorrelationId)), any(FiniteDuration.class));

        jBaker.processEvent(processUUID, testEvent, testCorrelationId);
        verify(mockBaker).processEvent(eq(processUUID.toString()), eq(testEvent), eq(Option.apply(testCorrelationId)), any(FiniteDuration.class));

        // with timeout

        jBaker.processEvent(processStringId, testEvent, testTimeout);
        verify(mockBaker).processEvent(eq(processStringId), eq(testEvent), eq(Option.empty()), eq(testTimeoutScala));

        jBaker.processEvent(processUUID, testEvent, testTimeout);
        verify(mockBaker).processEvent(eq(processUUID.toString()), eq(testEvent), eq(Option.empty()), eq(testTimeoutScala));

        // with correlation id and timeout

        jBaker.processEvent(processStringId, testEvent, testCorrelationId, testTimeout);
        verify(mockBaker).processEvent(eq(processStringId), eq(testEvent), eq(Option.apply(testCorrelationId)), eq(testTimeoutScala));

        jBaker.processEvent(processUUID, testEvent, testCorrelationId, testTimeout);
        verify(mockBaker).processEvent(eq(processUUID.toString()), eq(testEvent), eq(Option.apply(testCorrelationId)), eq(testTimeoutScala));
    }

    @Test
    public void shouldExecuteCompleteFlow() throws BakerException, TimeoutException {

        JBaker jBaker = new JBaker(actorSystem);

        jBaker.addImplementations(implementationsList);

        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(JavaCompiledRecipeTest.setupComplexRecipe());

        String recipeId = jBaker.addRecipe(compiledRecipe);

        String requestId = UUID.randomUUID().toString();
        jBaker.bake(recipeId, requestId);
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventOne());
        jBaker.processEvent(requestId, new JavaCompiledRecipeTest.EventTwo());
    }

    @Test
    public void shouldFailWhenSieveNotDefaultConstructor() throws BakerException {
        Recipe recipe = JavaCompiledRecipeTest.setupComplexRecipe()
                .withSieve(InteractionDescriptor.of(JavaCompiledRecipeTest.SieveImplWithoutDefaultConstruct.class));

        exception.expect(BakerException.class);
        CompiledRecipe compiledRecipe = RecipeCompiler.compileRecipe(recipe);

        JBaker jBaker = new JBaker(actorSystem);

        jBaker.addImplementations(implementationsList);

        jBaker.addRecipe(compiledRecipe);
    }

    final static class EmptySubscriber {
        @SuppressWarnings("unused")
        @Subscribe
        public void onEvent(ProcessCreated e) {
            // intentionally left empty
        }
    }

}
