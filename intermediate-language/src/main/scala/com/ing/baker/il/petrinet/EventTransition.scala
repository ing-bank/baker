package com.ing.baker.il.petrinet

import com.ing.baker.il.CompiledEvent

/**
  * Transition providing data from an event.
  */
case class EventTransition(event: CompiledEvent,
                           val isSensoryEvent: Boolean = true,
                           val isMissing: Boolean = false) extends Transition[Unit, CompiledEvent] {

  override val id       = (event.name + "EventTransition").hashCode.toLong
  override val label    = event.name
  override val toString = label
}
