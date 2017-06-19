package com.ing.baker.il.petrinet

import com.ing.baker.core.ProcessState

case class MissingEventTransition[E](override val id: Long, override val label: String) extends Transition[Unit, E]