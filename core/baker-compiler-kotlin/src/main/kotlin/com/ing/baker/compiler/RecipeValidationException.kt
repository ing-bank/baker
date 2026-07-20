package com.ing.baker.compiler

data class RecipeValidationException(val reason: String = ""): IllegalArgumentException(reason)
