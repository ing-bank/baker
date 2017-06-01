package com.ing.baker.newrecipe.common

trait Event {
  val name: String
  val providedIngredients: Seq[Ingredient]
}
