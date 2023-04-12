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
import com.ing.baker.runtime.javadsl.SensoryEventResult
import com.ing.baker.types.Value
import kotlinx.coroutines.future.asDeferred
import kotlinx.coroutines.future.await
import kotlinx.coroutines.runBlocking
import java.util.*

class Baker(private val jBaker: Baker) : AutoCloseable {
    override fun close() {
        // FIXME we should block here and wait for a max of 10 seconds
        runBlocking { gracefulShutdown() }
    }

    suspend fun addRecipe(recipeRecord: RecipeRecord): String = jBaker.addRecipe(recipeRecord).await()

    suspend fun addRecipe(compiledRecipe: CompiledRecipe, timeCreated: Long, validate: Boolean): String =
        addRecipe(RecipeRecord.of(compiledRecipe, timeCreated, validate))

    // TODO we could also support this via default arguments, but then our test won't work
    suspend fun addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean): String =
        addRecipe(compiledRecipe, System.currentTimeMillis(), validate)

    suspend fun gracefulShutdown() {
        jBaker.gracefulShutdown().await()
    }

    suspend fun bake(recipeId: String, recipeInstanceId: String) {
        jBaker.bake(recipeId, recipeInstanceId).await()
    }

    suspend fun bake(recipeId: String, recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.bake(recipeId, recipeInstanceId, metadata).await()
    }

    // TODO See if we can use nullabely types instead of optionals whilst keeping the overloads.
    suspend fun fireEventAndResolveWhenReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String
    ): SensoryEventStatus =
        fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.of(correlationId))

    suspend fun fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): SensoryEventStatus =
        fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.empty<String>())

    suspend fun fireEventAndResolveWhenReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: Optional<String>
    ): SensoryEventStatus =
        jBaker.fireEventAndResolveWhenReceived(recipeInstanceId, event, correlationId).await()

    suspend fun fireEventAndResolveWhenCompleted(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String
    ): SensoryEventResult =
        fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.of(correlationId))

    suspend fun fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): SensoryEventResult =
        fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.empty<String>())

    suspend fun fireEventAndResolveWhenCompleted(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: Optional<String>
    ): SensoryEventResult =
        jBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, event, correlationId)
            .await()
            .let { SensoryEventResult(it.sensoryEventStatus, it.eventNames, it.ingredients) }


    suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String,
        correlationId: String
    ): SensoryEventResult =
        fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.of(correlationId))

    suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String
    ): SensoryEventResult =
        fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.empty<String>())

    suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String,
        correlationId: Optional<String>
    ): SensoryEventResult =
        jBaker.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, correlationId)
            .await()
            .let { SensoryEventResult(it.sensoryEventStatus, it.eventNames, it.ingredients) }

    fun fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutions =
        fireEvent(recipeInstanceId, event, Optional.of(correlationId))

    fun fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutions =
        fireEvent(recipeInstanceId, event, Optional.empty<String>())

    fun fireEvent(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: Optional<String> // FIXME correlationID param is never used.
    ): EventResolutions =
        jBaker.fireEvent(recipeInstanceId, event)
            .let {
                EventResolutions(
                    resolveWhenReceived = it.resolveWhenReceived.asDeferred(),
                    resolveWhenCompleted = it.resolveWhenCompleted.asDeferred()
                )
            }

    suspend fun retryInteraction(recipeInstanceId: String, interactionName: String) =
        jBaker.retryInteraction(recipeInstanceId, interactionName).await()

    suspend fun resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance) =
        jBaker.resolveInteraction(recipeInstanceId, interactionName, event).await()

    suspend fun stopRetryingInteraction(recipeInstanceId: String, interactionName: String) =
        jBaker.stopRetryingInteraction(recipeInstanceId, interactionName).await()

    suspend fun getRecipeInstanceState(recipeInstanceId: String) =
        jBaker.getRecipeInstanceState(recipeInstanceId).await()

    suspend fun getIngredients(recipeInstanceId: String): Map<String, Value> =
        jBaker.getIngredients(recipeInstanceId).await()

    suspend fun getEvents(recipeInstanceId: String): List<EventMoment> =
        jBaker.getEvents(recipeInstanceId).await()

    suspend fun getEventNames(recipeInstanceId: String): List<String> =
        jBaker.getEventNames(recipeInstanceId).await()

    suspend fun getRecipe(recipeId: String): RecipeInformation =
        jBaker.getRecipe(recipeId).await()

    suspend fun getRecipeVisual(recipeId: String, style: RecipeVisualStyle): String =
        jBaker.getRecipeVisual(recipeId, style).await()

    suspend fun getAllRecipes(): Map<String, RecipeInformation> = jBaker.allRecipes.await()

    suspend fun getInteraction(interactionName: String): Optional<InteractionInstanceDescriptor> =
        jBaker.getInteraction(interactionName).await()

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
        listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit)
    ) {
        jBaker.registerEventListener(recipeName, listenerFunction).await()
    }

    suspend fun registerEventListener(listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit)) {
        jBaker.registerEventListener(listenerFunction).await()
    }

    suspend fun registerBakerEventListener(listenerFunction: ((BakerEvent) -> Unit)) {
        jBaker.registerBakerEventListener(listenerFunction).await()
    }

    suspend fun getVisualState(recipeInstanceId: String): String =
        jBaker.getVisualState(recipeInstanceId, RecipeVisualStyle.default()).await()

    suspend fun getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): String =
        jBaker.getVisualState(recipeInstanceId, style).await()

    suspend fun addMetaData(recipeInstanceId: String, metadata: Map<String, String>) {
        jBaker.addMetaData(recipeInstanceId, metadata).await()
    }
}
