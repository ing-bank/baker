package com.ing.baker.recipe

import com.ing.baker.types.Type

interface IngredientDescriptor {
    val name: String
    val type: Type
}
