package com.ing.baker.recipe

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.Value

interface InteractionDescriptor {
    val name: String
    val originalName: String
    val inputIngredients: List<Ingredient>
    val output: List<Event>
    val requiredEvents: Set<String>
    val requiredOneOfEvents: Set<Set<String>>
    val predefinedIngredients: Map<String, Value>
    val overriddenIngredientNames: Map<String, String>
    val overriddenOutputIngredientName: String?
    val eventOutputTransformers: Map<Event, EventOutputTransformer>
    val maximumInteractionCount: Int?
    val failureStrategy: InteractionFailureStrategy?
    val isReprovider: Boolean
}