package com.ing.baker.recipe.common

trait Ingredient {
  val name: String
  val clazz: Class[_]

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Ingredient => this.name == other.name && this.clazz == other.clazz
    case _ => false
  }

  override def toString: String = s"$name: ${clazz.getSimpleName}"
}
