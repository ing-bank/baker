package com.ing.baker.il

import java.lang.reflect.Field

case class IngredientType(name: String, clazz: Class[_])

object IngredientType{
  def apply(obj: Any): IngredientType =
    IngredientType(obj.getClass.getSimpleName, obj.getClass)

  def apply(field: Field): IngredientType =
    IngredientType(field.getName, field.getType)
}
