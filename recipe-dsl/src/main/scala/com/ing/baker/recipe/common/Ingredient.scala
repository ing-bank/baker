package com.ing.baker.recipe.common

import java.lang.reflect.Type

trait Ingredient {
  val name: String
  val clazz: Type

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Ingredient => this.name == other.name && this.clazz == other.clazz
    case _ => false
  }
}
