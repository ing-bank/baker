package com.ing.baker.newrecipe.common

trait Ingredient {
  val name: String
  val clazz: Class[_]

  override def equals(obj: scala.Any): Boolean = obj match {
    case ingredient: Ingredient => this.name == ingredient.name && this.clazz == ingredient.clazz
    case _ => false
  }

  override def toString: String = s"Ingredient: $name -> ${clazz.getSimpleName}"
}
