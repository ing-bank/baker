package com.ing.baker.recipe

import com.ing.baker.recipe.common.InteractionFailureStrategy
import kotlin.time.Duration

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