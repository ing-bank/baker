package com.ing.baker.compiledRecipe

import java.lang.reflect.Field

case class RuntimeIngredient(name: String,
                             clazz: Class[_]) {
  override def equals(obj: scala.Any): Boolean = obj match {
    case other: RuntimeIngredient =>
      this.name == other.name &&
      this.clazz == other.clazz
    case _ => false
  }
}

object RuntimeIngredient{
  def apply(obj: Any): RuntimeIngredient =
    RuntimeIngredient(obj.getClass.getSimpleName, obj.getClass)

  def apply(field: Field): RuntimeIngredient =
    RuntimeIngredient(field.getName, field.getType)
}
