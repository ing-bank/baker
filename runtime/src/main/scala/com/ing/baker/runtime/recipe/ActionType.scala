package com.ing.baker.runtime.recipe

sealed trait ActionType

object ActionType {
  case object SieveAction       extends ActionType
  case object InteractionAction extends ActionType
}
