package com.ing.baker.il

/**
  * Describes an event.
  *
  * @param name The name of an event.
  * @param ingredientTypes The ingredients the event produces.
  */
case class EventType(name: String,
                     ingredientTypes: Seq[IngredientDescriptor])