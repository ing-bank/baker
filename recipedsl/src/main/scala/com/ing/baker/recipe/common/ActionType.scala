package com.ing.baker.recipe.common

sealed trait ActionType

object ActionType {
  case object SieveAction       extends ActionType
  case object InteractionAction extends ActionType
}
