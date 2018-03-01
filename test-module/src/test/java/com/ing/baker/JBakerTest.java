package com.ing.baker;

import com.google.common.collect.ImmutableList;
import com.ing.baker.compiler.JavaCompiledRecipeTest;
import com.ing.baker.compiler.RecipeCompiler;
import com.ing.baker.il.CompiledRecipe;
import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import com.ing.baker.runtime.core.Baker;
import com.ing.baker.runtime.core.BakerException;
import com.ing.baker.runtime.core.EventListener;
import com.ing.baker.runtime.java_api.JBaker;
import com.ing.baker.types.Converters;
import com.typesafe.config.ConfigFactory;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import scala.Option;
import scala.collection.immutable.List;
import scala.collection.immutable.List$;
import scala.concurrent.duration.FiniteDuration;

import java.util.Collections;
import java.util.UUID;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupComplexRecipe;
import static com.ing.baker.compiler.JavaCompiledRecipeTest.setupSimpleRecipe;
import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.*;

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
        EventListener testListener = (processId, event) -> { };

        when(mockBaker.eventNames(any(String.class), any(FiniteDuration.class))).thenReturn(List$.MODULE$.empty());

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

        jBaker.getAllRecipes();
        verify(mockBaker).getAllRecipes(any(FiniteDuration.class));

        jBaker.getCompiledRecipe(testRecipeId);
        verify(mockBaker).getRecipe(eq(testRecipeId), any(FiniteDuration.class));

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
