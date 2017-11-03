package com.ing.baker.il

import com.ing.baker.il.types.IngredientDescriptor

case class EventType(name: String, ingredientTypes: Seq[IngredientDescriptor])