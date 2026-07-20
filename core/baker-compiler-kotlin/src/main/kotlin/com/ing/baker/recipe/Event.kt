package com.ing.baker.recipe

data class Event(
    val name: String,
    val providedIngredients: List<Ingredient>,
    val maxFiringLimit: Int? = null,
)