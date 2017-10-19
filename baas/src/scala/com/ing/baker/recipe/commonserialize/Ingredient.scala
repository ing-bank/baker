package com.ing.baker.recipe.commonserialize

import java.lang.reflect.Type

import com.ing.baker.recipe.common

case class Ingredient(override val name: String,
                      typeName: String) extends common.Ingredient {

  @transient
  val clazz: Type = Class.forName(typeName)

  def this(ingredient: common.Ingredient) = this(ingredient.name, ingredient.clazz.getTypeName)
}