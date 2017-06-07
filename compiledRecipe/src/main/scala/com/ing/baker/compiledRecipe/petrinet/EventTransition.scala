package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.RuntimeEvent
import com.ing.baker.core.ProcessState

/**
  * Transition providing data from an event.
  */
//TODO remove E since its always RuntimeEvent
case class EventTransition(event: RuntimeEvent,
                              val isSensoryEvent: Boolean = true,
                              val isMissing: Boolean = false) extends Transition[Unit, RuntimeEvent, ProcessState] {

  override val id       = (event.name + "EventTransition").hashCode.toLong
  override val label    = event.name
  override val toString = label
}
