package com.ing.baker.newrecipe.common

trait Ingredient {
  val name: String
  val clazz: Class[_]

  override def equals(obj: scala.Any): Boolean = obj match {
    case other: Ingredient => this.name == other.name && this.clazz == other.clazz
    case _ => false
  }
}
