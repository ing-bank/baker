package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

case class Ingredient(nameInput: String, ingredientTypeInput: java.lang.reflect.Type)
  extends common.Ingredient(nameInput, Converters.readJavaType(ingredientTypeInput))
