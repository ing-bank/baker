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
import kotlin.time.Duration.Companion.seconds

class CoroutineBaker(private val jBaker: Baker) : com.ing.baker.runtime.kotlindsl.Baker, AutoCloseable {
    override fun close() = runBlocking {
        withTimeout(10.seconds) {
            gracefulShutdown()
        }
    }

    override suspend fun gracefulShutdown() {
        jBaker.gracefulShutdown().await()
    }

    override suspend fun addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean, timeCreated: Long): String =
        addRecipe(RecipeRecord.of(compiledRecipe, timeCreated, validate))

    override suspend fun addRecipe(recipeRecord: RecipeRecord): String =
        jBaker.addRecipe(recipeRecord).await()

    override suspend fun bake(recipeId: String, recipeInstanceId: String) {
        jBaker.bake(recipeId, recipeInstanceId).await()
    }

    override suspend fun bake(recipeId: String, recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.bake(recipeId, recipeInstanceId, metadata).await()
    }

    override suspend fun fireEventAndResolveWhenReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String?
    ): SensoryEventStatus {
       return jBaker.fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.ofNullable(correlationId))
           .await()
    }

    override suspend fun fireEventAndResolveWhenCompleted(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String?
    ): SensoryEventResult {
        return jBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .await()
    }

    override suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String,
        correlationId: String?
    ): SensoryEventResult {
        return jBaker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.ofNullable(correlationId))
            .await()
    }

    override fun fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String?): EventResolutions {
        return jBaker.fireEvent(recipeInstanceId, event, Optional.ofNullable(correlationId))
            .let {
                EventResolutions(
                    resolveWhenReceived = it.resolveWhenReceived.asDeferred(),
                    resolveWhenCompleted = it.resolveWhenCompleted.asDeferred()
                )
            }
    }

    override suspend fun retryInteraction(recipeInstanceId: String, interactionName: String) {
        jBaker.retryInteraction(recipeInstanceId, interactionName).await()
    }

    override suspend fun resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance) {
        jBaker.resolveInteraction(recipeInstanceId, interactionName, event).await()
    }

    override suspend fun stopRetryingInteraction(recipeInstanceId: String, interactionName: String) {
        jBaker.stopRetryingInteraction(recipeInstanceId, interactionName).await()
    }

    override suspend fun getRecipeInstanceState(recipeInstanceId: String): RecipeInstanceState =
        jBaker.getRecipeInstanceState(recipeInstanceId).await()

    override suspend fun getIngredients(recipeInstanceId: String): Map<String, Value> =
        jBaker.getIngredients(recipeInstanceId).await()

    override suspend fun getEvents(recipeInstanceId: String): List<EventMoment> =
        jBaker.getEvents(recipeInstanceId).await()

    override suspend fun getEventNames(recipeInstanceId: String): List<String> =
        jBaker.getEventNames(recipeInstanceId).await()

    override suspend fun getRecipe(recipeId: String): RecipeInformation =
        jBaker.getRecipe(recipeId).await()

    override suspend fun getRecipeVisual(recipeId: String, style: RecipeVisualStyle): String =
        jBaker.getRecipeVisual(recipeId, style).await()

    override suspend fun getAllRecipes(): Map<String, RecipeInformation> = jBaker.allRecipes.await()

    override suspend fun getInteraction(interactionName: String): Optional<InteractionInstanceDescriptor> =
        jBaker.getInteraction(interactionName).await()

    override suspend fun getAllInteractions(): List<InteractionInstanceDescriptor> =
        jBaker.allInteractions.await()

    override suspend fun executeSingleInteraction(
        interactionId: String,
        ingredients: List<IngredientInstance>
    ): InteractionExecutionResult =
        jBaker.executeSingleInteraction(interactionId, ingredients).await()

    override suspend fun getAllRecipeInstancesMetadata(): Set<RecipeInstanceMetadata> =
        jBaker.allRecipeInstancesMetadata.await()

    override suspend fun registerEventListener(
        recipeName: String,
        listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit)
    ) {
        jBaker.registerEventListener(recipeName, listenerFunction).await()
    }

    override suspend fun registerEventListener(listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit)) {
        jBaker.registerEventListener(listenerFunction).await()
    }

    override suspend fun registerBakerEventListener(listenerFunction: ((BakerEvent) -> Unit)) {
        jBaker.registerBakerEventListener(listenerFunction).await()
    }

    override suspend fun getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): String =
        jBaker.getVisualState(recipeInstanceId, style).await()

    override suspend fun addMetaData(recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.addMetaData(recipeInstanceId, metadata).await()
    }
}
