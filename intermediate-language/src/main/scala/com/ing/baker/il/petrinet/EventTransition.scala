package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.EventDescriptor

/**
  * Transition providing data from an event.
  */
case class EventTransition(event: EventDescriptor,
                           isSensoryEvent: Boolean = true,
                           maxFiringLimit: Option[Integer] = None
                          ) extends Transition[Unit, EventDescriptor] {

  override val label: String = event.name
  override val id: Long = il.sha256HashCode(s"EventTransition:$label")
  override val toString: String = label
}
