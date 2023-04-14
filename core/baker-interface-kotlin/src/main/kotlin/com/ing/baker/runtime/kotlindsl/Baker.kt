package com.ing.baker.runtime.kotlindsl

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
import com.ing.baker.types.Value
import java.util.*

interface Baker {
    suspend fun gracefulShutdown()

    suspend fun addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean, timeCreated: Long = System.currentTimeMillis()): String

    suspend fun addRecipe(recipeRecord: RecipeRecord): String

    suspend fun bake(recipeId: String, recipeInstanceId: String)

    suspend fun bake(recipeId: String, recipeInstanceId: String, metadata: Map<String, String>)

    suspend fun fireEventAndResolveWhenReceived(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventStatus

    suspend fun fireEventAndResolveWhenCompleted(
        recipeInstanceId: String,
        event: EventInstance,
        correlationId: String? = null
    ): SensoryEventResult

    suspend fun fireEventAndResolveOnEvent(
        recipeInstanceId: String,
        event: EventInstance,
        onEvent: String,
        correlationId: String? = null
    ): SensoryEventResult

    fun fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String? = null): EventResolutions

    suspend fun retryInteraction(recipeInstanceId: String, interactionName: String)

    suspend fun resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance)

    suspend fun stopRetryingInteraction(recipeInstanceId: String, interactionName: String)

    suspend fun getRecipeInstanceState(recipeInstanceId: String): RecipeInstanceState

    suspend fun getIngredients(recipeInstanceId: String): Map<String, Value>

    suspend fun getEvents(recipeInstanceId: String): List<EventMoment>

    suspend fun getEventNames(recipeInstanceId: String): List<String>

    suspend fun getRecipe(recipeId: String): RecipeInformation

    suspend fun getRecipeVisual(recipeId: String, style: RecipeVisualStyle = RecipeVisualStyle.default()): String

    suspend fun getAllRecipes(): Map<String, RecipeInformation>

    suspend fun getInteraction(interactionName: String): Optional<InteractionInstanceDescriptor>

    suspend fun getAllInteractions(): List<InteractionInstanceDescriptor>

    suspend fun executeSingleInteraction(interactionId: String, ingredients: List<IngredientInstance>): InteractionExecutionResult

    suspend fun getAllRecipeInstancesMetadata(): Set<RecipeInstanceMetadata>

    suspend fun registerEventListener(recipeName: String, listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit))

    suspend fun registerEventListener(listenerFunction: ((RecipeEventMetadata, EventInstance) -> Unit))

    suspend fun registerBakerEventListener(listenerFunction: ((BakerEvent) -> Unit))

    suspend fun getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default()): String

    suspend fun addMetaData(recipeInstanceId: String, metadata: Map<String, String>)
}