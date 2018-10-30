package com.ing.baker.recipe.common

import com.ing.baker.types.Type

class Ingredient(val name: String,
                 val ingredientType: Type) {

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Ingredient => this.name == other.name && this.ingredientType == other.ingredientType
    case _ => false
  }

  override def toString: String = s"Ingredient($name, $ingredientType)"
}
