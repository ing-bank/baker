package com.ing.baker.il.petrinet

import com.ing.baker.il

case class IntermediateTransition(override val label: String) extends Transition {
  override val id: Long = il.sha256HashCode(s"IntermediateTransition:$label")
}
