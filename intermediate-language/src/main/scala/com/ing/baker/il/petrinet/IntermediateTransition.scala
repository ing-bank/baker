package com.ing.baker.il.petrinet

import com.ing.baker.il

case class IntermediateTransition(override val label: String) extends Transition[Unit, Unit] {
  override def id: Long = il.sha256HashCode(s"IntermediateTransition:$label")
}
