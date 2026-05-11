package com.ing.baker.recipe

import com.ing.baker.types.Type

data class Ingredient(override val name: String, override val type: Type): IngredientDescriptor