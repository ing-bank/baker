package com.ing.baker.il

import java.lang.reflect.Field

case class CompiledIngredient(name: String,
                              clazz: Class[_])
object CompiledIngredient{
  def apply(obj: Any): CompiledIngredient =
    CompiledIngredient(obj.getClass.getSimpleName, obj.getClass)

  def apply(field: Field): CompiledIngredient =
    CompiledIngredient(field.getName, field.getType)
}
