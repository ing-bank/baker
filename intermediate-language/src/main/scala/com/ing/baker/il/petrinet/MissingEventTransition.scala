package com.ing.baker.il.petrinet

import com.ing.baker.il

case class MissingEventTransition[E](override val label: String) extends Transition[Unit, E] {
  override def id: Long = il.sha256HashCode(s"MissingEventTransition:$label")
}