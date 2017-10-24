package com.ing.baker.recipe.commonserialize

import java.lang.reflect.Type

import com.ing.baker.recipe.common

case class Ingredient(override val name: String,
                      override val clazz: Type) extends common.Ingredient {

//  val clazz: Type = Class.forName(typeName)

  def this(ingredient: common.Ingredient) = this(ingredient.name, ingredient.clazz)

  override def equals(obj: Any): Boolean = {
    if (!obj.isInstanceOf[common.Ingredient])
      return false
    val other: common.Ingredient = obj.asInstanceOf[common.Ingredient]
    this.name == other.name
    this.clazz == other.clazz
  }
}