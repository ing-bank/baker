package com.ing.baker.runtime.kotlindsl

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.RecipeVisualStyle
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.javadsl.Baker
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
import com.ing.baker.types.Value
import kotlinx.coroutines.future.asDeferred
import kotlinx.coroutines.future.await
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import java.util.*
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.toJavaDuration

class Baker internal constructor(private val jBaker: Baker) : AutoCloseable {
    override fun close() = runBlocking {
        withTimeout(10.seconds) {
            gracefulShutdown()
        }
    }

    fun getJavaBaker(): Baker {
        return jBaker
    }

    suspend fun gracefulShutdown() {
        jBaker.gracefulShutdown().await()
    }

    suspend fun addRecipe(
        compiledRecipe: CompiledRecipe,
        validate: Boolean,
        timeCreated: Long = System.currentTimeMillis()
    ): String =
        addRecipe(RecipeRecord.of(compiledRecipe, timeCreated, validate, true))

    private suspend fun addRecipe(recipeRecord: RecipeRecord): String =
        jBaker.addRecipe(recipeRecord).await()

    suspend fun bake(recipeId: String, recipeInstanceId: String) {
        jBaker.bake(recipeId, recipeInstanceId).await()
    }

    suspend fun bake(recipeId: String, recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.bake(recipeId, recipeInstanceId, metadata).await()
    }

    suspend fun deleteRecipeInstance(recipeInstanceId: String, removeFromIndex: Boolean = false) {
        jBaker.deleteRecipeInstance(recipeInstanceId, removeFromIndex).await()
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
        return jBaker.fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.ofNullable(correlationId))
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
        return jBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.ofNullable(correlationId))
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
        return jBaker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.ofNullable(correlationId))
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
    ): EventResolutions {
        return jBaker.fireEvent(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .let {
                EventResolutions(
                    resolveWhenReceived = it.resolveWhenReceived.asDeferred(),
                    resolveWhenCompleted = it.resolveWhenCompleted.asDeferred()
                )
            }
    }

    suspend fun retryInteraction(recipeInstanceId: String, interactionName: String) {
        jBaker.retryInteraction(recipeInstanceId, interactionName).await()
    }

    suspend fun resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance) {
        jBaker.resolveInteraction(recipeInstanceId, interactionName, event).await()
    }

    suspend fun stopRetryingInteraction(recipeInstanceId: String, interactionName: String) {
        jBaker.stopRetryingInteraction(recipeInstanceId, interactionName).await()
    }

    suspend fun hasRecipeInstance(recipeInstanceId: String): Boolean =
        // Explicit cast since the method returns scala.Boolean and implicit conversion is not available
        jBaker.hasRecipeInstance(recipeInstanceId).await() as Boolean

    suspend fun getRecipeInstanceState(recipeInstanceId: String): RecipeInstanceState =
        jBaker.getRecipeInstanceState(recipeInstanceId).await()

    suspend fun getIngredients(recipeInstanceId: String): Map<String, Value> =
        jBaker.getIngredients(recipeInstanceId).await()

    suspend fun getIngredient(recipeInstanceId: String, name: String): Value =
        jBaker.getIngredient(recipeInstanceId, name).await()

    suspend fun getEvents(recipeInstanceId: String): List<EventMoment> =
        jBaker.getEvents(recipeInstanceId).await()

    suspend fun getEventNames(recipeInstanceId: String): List<String> =
        jBaker.getEventNames(recipeInstanceId).await()

    suspend fun getRecipe(recipeId: String): RecipeInformation =
        jBaker.getRecipe(recipeId).await()

    suspend fun getRecipeVisual(recipeId: String, style: RecipeVisualStyle = RecipeVisualStyle.default()): String =
        jBaker.getRecipeVisual(recipeId, style).await()

    suspend fun getAllRecipes(): Map<String, RecipeInformation> = jBaker.allRecipes.await()

    suspend fun getInteraction(interactionName: String): InteractionInstanceDescriptor? =
        jBaker.getInteraction(interactionName).await().toNullable()

    suspend fun getAllInteractions(): List<InteractionInstanceDescriptor> =
        jBaker.allInteractions.await()

    suspend fun executeSingleInteraction(
        interactionId: String,
        ingredients: List<IngredientInstance>
    ): InteractionExecutionResult =
        jBaker.executeSingleInteraction(interactionId, ingredients).await()

    suspend fun getAllRecipeInstancesMetadata(): Set<RecipeInstanceMetadata> =
        jBaker.allRecipeInstancesMetadata.await()

    suspend fun registerEventListener(
        recipeName: String,
        listenerFunction: (RecipeEventMetadata, String) -> Unit
    ) {
        jBaker.registerEventListener(recipeName, listenerFunction).await()
    }

    suspend fun registerEventListener(listenerFunction: (RecipeEventMetadata, String) -> Unit) {
        jBaker.registerEventListener(listenerFunction).await()
    }

    suspend fun registerBakerEventListener(listenerFunction: (BakerEvent) -> Unit) {
        jBaker.registerBakerEventListener(listenerFunction).await()
    }

    suspend fun getVisualState(
        recipeInstanceId: String,
        style: RecipeVisualStyle = RecipeVisualStyle.default()
    ): String =
        jBaker.getVisualState(recipeInstanceId, style).await()

    suspend fun addMetaData(recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.addMetaData(recipeInstanceId, metadata).await()
    }

    suspend fun fireSensoryEventAndAwaitReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventStatus {
        return jBaker.fireSensoryEventAndAwaitReceived(
            recipeInstanceId,
            event,
            Optional.ofNullable(correlationId),
        ).await()
    }

    suspend fun awaitEvent(
        recipeInstanceId: String,
        eventName: String,
        timeout: Duration,
        waitForNext: Boolean = false
    ) {
        jBaker.awaitEvent(recipeInstanceId, eventName, timeout.toJavaDuration(), waitForNext).await()
    }

    suspend fun awaitCompleted(
        recipeInstanceId: String,
        timeout: Duration,
    ): SensoryEventStatus {
        return jBaker.awaitCompleted(recipeInstanceId, timeout.toJavaDuration()).await()
    }

    private fun <T> Optional<T>.toNullable(): T? = if (isEmpty) null else get()
}
