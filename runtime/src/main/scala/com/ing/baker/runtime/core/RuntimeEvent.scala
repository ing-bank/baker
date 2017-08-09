package com.ing.baker.runtime.core

import com.ing.baker.il.{EventType, IngredientType}


case class RuntimeEvent(name: String,
                        providedIngredients: Map[String, Any]) {
  /**
    * the EventType of this RuntimeEvent (meta information of this event)
    */
  val eventType: EventType = EventType(name, providedIngredients.map {
    case (ingredientName, ingredientValue) => IngredientType(ingredientName, ingredientValue.getClass)
  }.toSeq)
}