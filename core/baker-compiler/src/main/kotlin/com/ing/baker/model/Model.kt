package com.ing.baker.model

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.Type
import kotlin.collections.mapValues
import kotlin.collections.toMap
import kotlin.time.Duration
import java.lang.reflect.Type as JavaType
import com.ing.baker.types.Converters
import com.ing.baker.types.Value

data class Event(
    val name: String,
    val providedIngredients: List<Ingredient>,
    val maxFiringLimit: Int? = null,
)

data class CheckPointEvent(
    val name: String = "",
    val requiredEvents: Set<String> = emptySet(),
    val requiredOneOfEvents: Set<Set<String>> = emptySet(),
)

data class Ingredient(val name: String, val type: Type)

data class Recipe(
    val name: String,
    val interactions: List<Interaction>,
    val sensoryEvents: Set<Event>,
    val subRecipes: Set<Recipe>,
    val defaultFailureStrategy: InteractionFailureStrategy,
    val eventReceivePeriod: Duration? = null,
    val retentionPeriod: Duration? = null,
    val checkpointEvents: Set<CheckPointEvent>,
    val sieves: Set<Sieve>,
)

data class Sieve(
    val name: String = "",
    val inputIngredients: List<Ingredient>,
    val output: List<Event>,
    val function: Any,
    val javaTypes: List<JavaType>
)

data class EventOutputTransformer(val newEventName: String, val ingredientRenames: Map<String, String>)

data class Interaction(
    val name: String,
    val originalName: String,
    val inputIngredients: List<Ingredient>,
    val output: List<Event>,
    val requiredEvents: Set<String>,
    val requiredOneOfEvents: Set<Set<String>>,
    val predefinedIngredients: Map<String, Value>,
    val overriddenIngredientNames: Map<String, String>,
    val overriddenOutputIngredientName: String? = null,
    val eventOutputTransformers: Map<Event, EventOutputTransformer>,
    val maximumInteractionCount: Int? = null,
    val failureStrategy: InteractionFailureStrategy? = null,
    val isReprovider: Boolean
) {
    companion object {
        @JvmStatic
        fun of(
            name: String,
            interaction: Interaction,
            requiredEvents: Set<String>,
            requiredOneOfEvents: Set<Set<String>>,
            predefinedIngredients: Map<String, Any>,
            overriddenIngredientNames: Map<String, String>,
            eventOutputTransformers: Map<Event, EventOutputTransformer>,
            maximumInteractionCount: Int?,
            failureStrategy: InteractionFailureStrategy?,
            isReprovider: Boolean,
        ): Interaction =
            Interaction(
                name,
                interaction.originalName,
                interaction.inputIngredients,
                interaction.output,
                requiredEvents,
                requiredOneOfEvents,
                predefinedIngredients.mapValues { Converters.toValue(it.value) },
                overriddenIngredientNames,
                overriddenOutputIngredientName = null,
                eventOutputTransformers,
                maximumInteractionCount,
                failureStrategy,
                isReprovider
            )

        @JvmStatic
        fun of(
            name: String,
            originalName: String,
            inputIngredients: Set<Ingredient>,
            output: Set<Event>,
            requiredEvents: Set<String>,
            requiredOneOfEvents: Set<Set<String>>,
            predefinedIngredients: Map<String, Any>,
            overriddenIngredientNames: Map<String, String>,
            eventOutputTransformers: Map<Event, EventOutputTransformer>,
            maximumInteractionCount: Int?,
            failureStrategy: InteractionFailureStrategy?,
            isReprovider: Boolean
        ): Interaction =
            Interaction(
                name,
                originalName,
                inputIngredients.toList(),
                output.toList(),
                requiredEvents,
                requiredOneOfEvents,
                predefinedIngredients.mapValues { Converters.toValue(it.value) },
                overriddenIngredientNames.toMap(),
                overriddenOutputIngredientName = null,
                eventOutputTransformers,
                maximumInteractionCount,
                failureStrategy,
                isReprovider
            )
    }
}
