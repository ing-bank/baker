package com.ing.baker.petrinet.akka

import com.ing.baker.petrinet.runtime.EventSourcing.Event

/**
 * Wrapper class for publishing events from a petri net instance on the akka event bus.
 */
case class PetriNetInstanceEvent(processType: String, processId: String, event: Event)