package com.ing.baker.il

/**
  * Describes an event.
  *
  * @param name The name of an event.
  * @param ingredients The ingredients the event produces.
  */
case class EventDescriptor(name: String,
                           ingredients: Seq[IngredientDescriptor])