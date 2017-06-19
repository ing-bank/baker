package com.ing.baker.il.petrinet

case class IntermediateTransition(override val id: Long, override val label: String) extends Transition[Unit, Unit]
