package com.ing.baker.compiledRecipe

sealed trait ActionType

object ActionType {
  case object SieveAction       extends ActionType
  case object InteractionAction extends ActionType
}
