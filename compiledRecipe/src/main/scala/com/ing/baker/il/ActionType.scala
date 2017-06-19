package com.ing.baker.il

sealed trait ActionType

object ActionType {
  case object SieveAction       extends ActionType
  case object InteractionAction extends ActionType
}
