package com.ing.baker.recipe

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.Converters
import com.ing.baker.types.Value

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
            inputIngredients: List<Ingredient>,
            output: List<Event>,
            requiredEvents: Set<String> = emptySet(),
            requiredOneOfEvents: Set<Set<String>> = emptySet(),
        ): Interaction =
            Interaction(
                name,
                originalName = name,
                inputIngredients,
                output,
                requiredEvents,
                requiredOneOfEvents,
                predefinedIngredients = emptyMap(),
                overriddenIngredientNames = emptyMap(),
                overriddenOutputIngredientName = null,
                eventOutputTransformers = emptyMap(),
                maximumInteractionCount = null,
                failureStrategy = null,
                isReprovider = false
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