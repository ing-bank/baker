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
    * This checks if the runtime event is an instance of a event type.
    * @param eventType
    * @return
    */
  def isInstanceOfEventType(eventType: EventType): Boolean = {

    val namesMatch = eventType.name == name

    // we check all the required ingredient types, additional ones are ignored
    val typesMatch = eventType.ingredientTypes.forall { ingredientType =>
      providedIngredientsMap.get(ingredientType.name) match {
        case None        => false
        // we can only check the class since the type parameters are available on objects
        case Some(value) => ingredientType.clazz.isInstance(value)
      }
    }

    namesMatch && typesMatch
  }
}