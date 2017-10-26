package com.ing.baker.runtime.core

import com.ing.baker.il.{EventType, IngredientDescriptor}


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
  def isInstanceOfEventType(eventType: EventType): Boolean = validateEvent(eventType).isEmpty

  /**
    *
    * Validates the runtime event against a event type and returns a sequence
    * of validation errors.
    *
    * @param eventType The event type to validate against.
    * @return
    */
  def validateEvent(eventType: EventType): Seq[String] = {

    if (eventType.name != name)
      Seq(s"Provided event with name '$name' does not match expected name '${eventType.name}'")
    else
      // we check all the required ingredient types, additional ones are ignored
      eventType.ingredientTypes.flatMap { ingredientType =>
        providedIngredientsMap.get(ingredientType.name) match {
          case None        =>
            Seq(s"no value was provided for ingredient '${ingredientType.name}'")
          case Some(null)  =>
            Seq(s"null is not allowed as an ingredient value for '${ingredientType.name}'")
          // we can only check the class since the type parameters are available on objects
          case Some(value) if !(ingredientType.clazz.isInstance(value))  =>
            Seq(s"value is not of the correct type for ingredient '${ingredientType.name}'")
          case _ =>
            Seq.empty
        }
    }
  }
}