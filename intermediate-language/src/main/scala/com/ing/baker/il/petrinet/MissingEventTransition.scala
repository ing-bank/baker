package com.ing.baker.il.petrinet

case class MissingEventTransition[E](override val id: Long, override val label: String) extends Transition[Unit, E]