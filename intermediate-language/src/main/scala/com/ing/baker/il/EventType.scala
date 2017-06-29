package com.ing.baker.il

case class EventType(name: String,
                     providedIngredients: Seq[IngredientType])

object EventType {
  def apply(obj: Any): EventType = {
    EventType(obj.getClass.getSimpleName, obj.getClass.getDeclaredFields.map(IngredientType(_)))
  }
}