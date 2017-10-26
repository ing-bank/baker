package com.ing.baker.recipe.common

class Ingredient(val name: String,
                 val ingredientType: IngredientType) {

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Ingredient => this.name == other.name && this.ingredientType == other.ingredientType
    case _ => false
  }
}
