package com.ing.baker.recipe.common

trait EventOutputTransformer {
  val newEventName: String
  val ingredientRenames: Map[String, String]

  override def toString: String = s"$newEventName, $ingredientRenames"
}
