package com.ing.baker.il.petrinet

import com.ing.baker.il
import com.ing.baker.il.EventType

/**
  * Transition providing data from an event.
  */
case class EventTransition(event: EventType,
                           isSensoryEvent: Boolean = true,
                           maxFiringLimit: Option[Integer] = None
                          ) extends Transition[Unit, EventType] {

  override val label: String = event.name
  override val id: Long = il.sha256HashCode(s"EventTransition:$label")
  override val toString: String = label
}
