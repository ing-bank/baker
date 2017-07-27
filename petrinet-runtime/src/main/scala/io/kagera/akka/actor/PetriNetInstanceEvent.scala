package io.kagera.akka.actor

import io.kagera.runtime.EventSourcing.Event

/**
 * Wrapper class for publishing events from a petri net instance on the akka event bus.
 */
case class PetriNetInstanceEvent(processType: String, processId: String, event: Event)