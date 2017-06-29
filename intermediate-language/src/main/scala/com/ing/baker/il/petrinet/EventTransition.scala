package com.ing.baker.il.petrinet

import com.ing.baker.il.EventType

/**
  * Transition providing data from an event.
  */
case class EventTransition(event: EventType,
                           val isSensoryEvent: Boolean = true) extends Transition[Unit, EventType] {

  override val id       = (event.name + "EventTransition").hashCode.toLong
  override val label    = event.name
  override val toString = label
}
