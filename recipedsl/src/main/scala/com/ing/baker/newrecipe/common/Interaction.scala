package com.ing.baker.newrecipe.common

trait Interaction {
  val name: String
  val inputIngredients: Seq[Ingredient]
  val output: Either[Seq[Event], Ingredient]
}
