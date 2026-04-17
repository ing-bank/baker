package com.ing.baker.recipe

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.Converters
import com.ing.baker.types.Value

data class Interaction(
    override val name: String,
    override val originalName: String?,
    override val inputIngredients: List<Ingredient>,
    override val output: List<Event>,
    override val requiredEvents: Set<String>,
    override val requiredOneOfEvents: Set<Set<String>>,
    override val predefinedIngredients: Map<String, Value>,
    override val overriddenIngredientNames: Map<String, String>,
    override val overriddenOutputIngredientName: String? = null,
    override val eventOutputTransformers: Map<Event, EventOutputTransformer>,
    override val maximumInteractionCount: Int? = null,
    override val failureStrategy: InteractionFailureStrategy? = null,
    override val isReprovider: Boolean
) : InteractionDescriptor {
    companion object {
        @JvmStatic
        fun of(
            name: String,
            originalName: String? = null,
            inputIngredients: Set<Ingredient> = emptySet(),
            output: Set<Event> = emptySet(),
            requiredEvents: Set<String> = emptySet(),
            requiredOneOfEvents: Set<Set<String>> = emptySet(),
            predefinedIngredients: Map<String, Any> = emptyMap(),
            overriddenIngredientNames: Map<String, String> = emptyMap(),
            eventOutputTransformers: Map<Event, EventOutputTransformer> = emptyMap(),
            maximumInteractionCount: Int? = null,
            failureStrategy: InteractionFailureStrategy? = null,
            isReprovider: Boolean = false
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
