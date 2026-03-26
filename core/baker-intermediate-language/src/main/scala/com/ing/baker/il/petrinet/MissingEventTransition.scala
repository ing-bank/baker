package com.ing.baker.il.petrinet

import com.ing.baker.il

case class MissingEventTransition(override val label: String) extends Transition {
  override def id: Long = il.sha256HashCode(s"MissingEventTransition:$label")
}