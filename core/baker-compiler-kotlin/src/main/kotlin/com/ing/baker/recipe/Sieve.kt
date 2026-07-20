package com.ing.baker.recipe

import java.lang.reflect.Type

data class Sieve(
    val name: String = "",
    val inputIngredients: List<Ingredient>,
    val output: List<Event>,
    val function: Any,
    val javaTypes: List<Type>
)