package com.ing.baker.il.petrinet

import com.ing.baker.il

case class MultiFacilitatorTransition(override val label: String) extends Transition[Unit] {
  override def id: Long = il.sha256HashCode(s"MultiFacilitatorTransition:$label")
}
