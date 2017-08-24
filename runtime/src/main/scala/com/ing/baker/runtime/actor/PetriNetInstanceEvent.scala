package com.ing.baker.runtime.actor

import com.ing.baker.petrinet.runtime.EventSourcing.Event

/**
 * Wrapper class for publishing events from a petri net instance on the akka event bus.
 */
case class PetriNetInstanceEvent(processType: String, processId: String, event: Event)
