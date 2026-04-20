package com.ing.baker.recipe

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.Converters
import com.ing.baker.types.Value

data class Interaction(
    override val name: String,
    val oldName: String? = null,
    override val inputIngredients: List<Ingredient> = emptyList(),
    override val output: List<Event> = emptyList(),
    override val requiredEvents: Set<String> = emptySet(),
    override val requiredOneOfEvents: Set<Set<String>> = emptySet(),
    override val predefinedIngredients: Map<String, Value> = emptyMap(),
    override val overriddenIngredientNames: Map<String, String> = emptyMap(),
    override val overriddenOutputIngredientName: String? = null,
    override val eventOutputTransformers: Map<Event, EventOutputTransformer> = emptyMap(),
    override val maximumInteractionCount: Int? = null,
    override val failureStrategy: InteractionFailureStrategy? = null,
    override val isReprovider: Boolean = false,
) : InteractionDescriptor {
    override val originalName get() = oldName ?: name
}
