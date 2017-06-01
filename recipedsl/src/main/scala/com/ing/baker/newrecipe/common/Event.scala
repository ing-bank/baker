package com.ing.baker.newrecipe.common

trait Event {
  val name: String
  val providedIngredients: Seq[Ingredient]

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Event => this.name == other.name && this.providedIngredients == other.providedIngredients
    case _ => false
  }
}
