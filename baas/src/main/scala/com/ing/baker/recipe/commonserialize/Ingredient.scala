package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.IngredientType

case class Ingredient(override val name: String,
                      override val ingredientType: IngredientType) extends common.Ingredient(name, ingredientType) {

  def this(ingredient: common.Ingredient) = this(ingredient.name, ingredient.ingredientType)

  override def equals(obj: Any): Boolean = {
    if (!obj.isInstanceOf[common.Ingredient])
      return false
    val other: common.Ingredient = obj.asInstanceOf[common.Ingredient]
    this.name == other.name && this.ingredientType == other.ingredientType
  }
}