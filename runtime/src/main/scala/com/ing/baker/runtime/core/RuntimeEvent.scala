package com.ing.baker.runtime.core

import com.ing.baker.il.{EventType, IngredientType}


case class RuntimeEvent(name: String,
                        providedIngredients: Seq[(String, Any)]) {

  /**
    * The provided ingredients in the form of a Map
    * This is useful when a EventListener is used in Java.
    */
  val providedIngredientsMap: Map[String, Any] = providedIngredients.toMap;

  /**
    * the EventType of this RuntimeEvent (meta information of this event)
    */
  val eventType: EventType = EventType(name, providedIngredients.map {
    case (ingredientName, ingredientValue) => IngredientType(ingredientName, ingredientValue.getClass)
  })
}