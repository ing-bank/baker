package com.ing.baker.recipe.common

trait Interaction {
  val name: String
  val inputIngredients: Seq[Ingredient]
  val output: InteractionOutput

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Interaction =>
      this.name == other.name && this.inputIngredients == other.inputIngredients && this.output == other.output
    case _ => false
  }
}
