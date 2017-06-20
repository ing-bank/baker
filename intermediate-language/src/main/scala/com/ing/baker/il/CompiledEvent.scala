package com.ing.baker.il

case class CompiledEvent(name: String,
                         providedIngredients: Seq[CompiledIngredient])

object CompiledEvent{
  def apply(obj: Any): CompiledEvent = {
    CompiledEvent(obj.getClass.getSimpleName, obj.getClass.getDeclaredFields.map(CompiledIngredient(_)))
  }
}