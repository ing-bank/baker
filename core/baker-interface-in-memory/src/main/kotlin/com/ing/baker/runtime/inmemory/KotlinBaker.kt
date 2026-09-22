package com.ing.baker.runtime.inmemory

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.RecipeVisualStyle
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.javadsl.BakerEvent
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.EventMoment
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionExecutionResult
import com.ing.baker.runtime.javadsl.InteractionInstanceDescriptor
import com.ing.baker.runtime.javadsl.RecipeEventMetadata
import com.ing.baker.runtime.javadsl.RecipeInformation
import com.ing.baker.runtime.javadsl.RecipeInstanceMetadata
import com.ing.baker.runtime.javadsl.RecipeInstanceState
import com.ing.baker.runtime.javadsl.SensoryEventResult
import com.ing.baker.runtime.model.BakerConfig
import com.ing.baker.types.Value
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.future.asDeferred
import kotlinx.coroutines.future.await
import kotlinx.coroutines.future.future
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import java.util.Optional
import java.util.concurrent.CompletableFuture
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.toJavaDuration
import com.ing.baker.runtime.javadsl.Baker as JavaBaker

/**
 * Coroutine-friendly adapter for the in-memory Baker runtime.
 *
 * This keeps a Java async boundary (`CompletableFuture`) while exposing suspend methods for Kotlin callers.
 */
class KotlinBaker private constructor(
    private val delegate: JavaBaker,
    private val scope: CoroutineScope
) : AutoCloseable {

    override fun close() = runBlocking {
        withTimeout(10.seconds) {
            gracefulShutdown()
        }
    }

    companion object {

        private fun defaultScope(): CoroutineScope = CoroutineScope(Dispatchers.Default)

        @JvmStatic
        @JvmOverloads
        fun fromJava(delegate: JavaBaker, scope: CoroutineScope = defaultScope()): KotlinBaker =
            KotlinBaker(delegate, scope)

        @JvmStatic
        @JvmOverloads
        fun java(
            config: BakerConfig = BakerConfig.default(),
            implementations: List<Any> = emptyList(),
            scope: CoroutineScope = defaultScope()
        ): KotlinBaker = KotlinBaker(InMemoryBaker.java(config, implementations), scope)

        /**
         * CompletableFuture-based factory for callers that avoid blocking during builder initialization.
         */
        @JvmStatic
        @JvmOverloads
        fun javaAsync(
            config: BakerConfig = BakerConfig.default(),
            implementations: List<Any> = emptyList(),
            scope: CoroutineScope = defaultScope()
        ): CompletableFuture<KotlinBaker> =
            InMemoryBaker.javaAsync(config, implementations).thenApply { javaBaker ->
                KotlinBaker(javaBaker, scope)
            }
    }

    fun getJavaBaker(): JavaBaker = delegate

    suspend fun addRecipe(
        compiledRecipe: CompiledRecipe,
        validate: Boolean,
        timeCreated: Long = System.currentTimeMillis()
    ): String =
        addRecipe(RecipeRecord.of(compiledRecipe, timeCreated, validate, true))

    private suspend fun addRecipe(recipeRecord: RecipeRecord): String =
        delegate.addRecipe(recipeRecord).await()

    fun addRecipeAsync(
        compiledRecipe: CompiledRecipe,
        validate: Boolean,
        timeCreated: Long = System.currentTimeMillis()
    ): CompletableFuture<String> = scope.future {
        addRecipe(compiledRecipe, validate, timeCreated)
    }

    suspend fun gracefulShutdown() {
        delegate.gracefulShutdown().await()
    }

    fun gracefulShutdownAsync(): CompletableFuture<Unit> = scope.future {
        gracefulShutdown()
    }

    suspend fun bake(recipeId: String, recipeInstanceId: String) {
        delegate.bake(recipeId, recipeInstanceId).await()
    }

    suspend fun bake(recipeId: String, recipeInstanceId: String, metadata: Map<String, String>) {
        delegate.bake(recipeId, recipeInstanceId, metadata).await()
    }

    fun bakeAsync(recipeId: String, recipeInstanceId: String): CompletableFuture<Unit> = scope.future {
        bake(recipeId, recipeInstanceId)
    }

    suspend fun deleteRecipeInstance(recipeInstanceId: String, removeFromIndex: Boolean = false) {
        delegate.deleteRecipeInstance(recipeInstanceId, removeFromIndex).await()
    }

    @Deprecated(
        "This method is deprecated and will be removed after December 1st, 2026. Please use fireSensoryEventAndAwaitReceived instead.",
        level = DeprecationLevel.WARNING
    )
    suspend fun fireEventAndResolveWhenReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventStatus {
        return delegate.fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .await()
    }

    @Deprecated(
        "This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitCompleted.",
        level = DeprecationLevel.WARNING
    )
    suspend fun fireEventAndResolveWhenCompleted(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventResult {
        return delegate.fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .await()
    }

    @Deprecated(
        "This method is deprecated and will be removed after December 1st, 2026. Please use the combination of fireSensoryEventAndAwaitReceived followed by awaitEvent.",
        level = DeprecationLevel.WARNING
    )
    suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String,
        correlationId: String? = null
    ): SensoryEventResult {
        return delegate.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.ofNullable(correlationId))
            .await()
    }

    @Deprecated(
        "This method uses a callback-style API that is deprecated and will be removed after December 1st, 2026. Please use the new composable API: fireSensoryEventAndAwaitReceived followed by awaitCompleted or awaitEvent.",
        level = DeprecationLevel.WARNING
    )
    fun fireEvent(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): KotlinEventResolutions {
        return delegate.fireEvent(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .let {
                KotlinEventResolutions(
                    resolveWhenReceived = it.resolveWhenReceived.asDeferred(),
                    resolveWhenCompleted = it.resolveWhenCompleted.asDeferred()
                )
            }
    }

    suspend fun retryInteraction(recipeInstanceId: String, interactionName: String) {
        delegate.retryInteraction(recipeInstanceId, interactionName).await()
    }

    suspend fun resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance) {
        delegate.resolveInteraction(recipeInstanceId, interactionName, event).await()
    }

    suspend fun stopRetryingInteraction(recipeInstanceId: String, interactionName: String) {
        delegate.stopRetryingInteraction(recipeInstanceId, interactionName).await()
    }

    suspend fun hasRecipeInstance(recipeInstanceId: String): Boolean =
        delegate.hasRecipeInstance(recipeInstanceId).await() as Boolean

    suspend fun getRecipeInstanceState(recipeInstanceId: String): RecipeInstanceState =
        delegate.getRecipeInstanceState(recipeInstanceId).await()

    suspend fun getIngredients(recipeInstanceId: String): Map<String, Value> =
        delegate.getIngredients(recipeInstanceId).await()

    suspend fun getIngredient(recipeInstanceId: String, name: String): Value =
        delegate.getIngredient(recipeInstanceId, name).await()

    suspend fun getEvents(recipeInstanceId: String): List<EventMoment> =
        delegate.getEvents(recipeInstanceId).await()

    suspend fun getEventNames(recipeInstanceId: String): List<String> =
        delegate.getEventNames(recipeInstanceId).await()

    suspend fun getRecipe(recipeId: String): RecipeInformation =
        delegate.getRecipe(recipeId).await()

    suspend fun getRecipeVisual(recipeId: String, style: RecipeVisualStyle = RecipeVisualStyle.default()): String =
        delegate.getRecipeVisual(recipeId, style).await()

    suspend fun getAllRecipes(): Map<String, RecipeInformation> = delegate.allRecipes.await()

    suspend fun getInteraction(interactionName: String): InteractionInstanceDescriptor? =
        delegate.getInteraction(interactionName).await().toNullable()

    suspend fun getAllInteractions(): List<InteractionInstanceDescriptor> =
        delegate.allInteractions.await()

    suspend fun executeSingleInteraction(
        interactionId: String,
        ingredients: List<IngredientInstance>
    ): InteractionExecutionResult =
        delegate.executeSingleInteraction(interactionId, ingredients).await()

    suspend fun getAllRecipeInstancesMetadata(): Set<RecipeInstanceMetadata> =
        delegate.allRecipeInstancesMetadata.await()

    suspend fun registerEventListener(
        recipeName: String,
        listenerFunction: (RecipeEventMetadata, String) -> Unit
    ) {
        delegate.registerEventListener(recipeName, listenerFunction).await()
    }

    suspend fun registerEventListener(listenerFunction: (RecipeEventMetadata, String) -> Unit) {
        delegate.registerEventListener(listenerFunction).await()
    }

    suspend fun registerBakerEventListener(listenerFunction: (BakerEvent) -> Unit) {
        delegate.registerBakerEventListener(listenerFunction).await()
    }

    suspend fun getVisualState(
        recipeInstanceId: String,
        style: RecipeVisualStyle = RecipeVisualStyle.default()
    ): String =
        delegate.getVisualState(recipeInstanceId, style).await()

    suspend fun addMetaData(recipeInstanceId: String, metadata: Map<String, String>) {
        delegate.addMetaData(recipeInstanceId, metadata).await()
    }

    suspend fun fireSensoryEventAndAwaitReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventStatus =
        delegate.fireSensoryEventAndAwaitReceived(
            recipeInstanceId,
            event,
            Optional.ofNullable(correlationId)
        ).await()

    fun fireSensoryEventAndAwaitReceivedAsync(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): CompletableFuture<SensoryEventStatus> = scope.future {
        fireSensoryEventAndAwaitReceived(recipeInstanceId, event, correlationId)
    }

    suspend fun awaitCompleted(recipeInstanceId: String, timeout: Duration): SensoryEventStatus =
        delegate.awaitCompleted(recipeInstanceId, timeout.toJavaDuration()).await()

    fun awaitCompletedAsync(recipeInstanceId: String, timeout: Duration): CompletableFuture<SensoryEventStatus> = scope.future {
        awaitCompleted(recipeInstanceId, timeout)
    }

    suspend fun awaitEvent(
        recipeInstanceId: String,
        eventName: String,
        timeout: Duration,
        waitForNext: Boolean = false
    ) {
        delegate.awaitEvent(recipeInstanceId, eventName, timeout.toJavaDuration(), waitForNext).await()
    }

    private fun <T> Optional<T>.toNullable(): T? = if (isEmpty) null else get()
}

