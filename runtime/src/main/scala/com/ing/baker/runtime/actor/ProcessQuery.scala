package com.ing.baker.runtime.actor

import akka.NotUsed
import akka.actor.ActorSystem
import akka.persistence.query.scaladsl._
import akka.stream.scaladsl._
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing._
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.actor.process_instance.{ProcessInstance, ProcessInstanceSerialization}
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.actor.serialization.{Encryption, ObjectSerializer}

object ProcessQuery {

  def eventsForInstance[P[_], T[_], S, E](processTypeName: String,
    processId: String,
    topology: PetriNet[P[_], T[_]],
    encryption: Encryption = NoEncryption,
    readJournal: CurrentEventsByPersistenceIdQuery,
    eventSourceFn: T[_] ⇒ (S ⇒ E ⇒ S))(implicit actorSystem: ActorSystem,
      placeIdentifier: Identifiable[P[_]],
      transitionIdentifier: Identifiable[T[_]]): Source[(Instance[P, T, S], Event), NotUsed] = {

    val serializer = new ProcessInstanceSerialization[P, T, S, E](new ObjectSerializer(actorSystem, encryption))

    val persistentId = ProcessInstance.processId2PersistenceId(processTypeName, processId)
    val src = readJournal.currentEventsByPersistenceId(persistentId, 0, Long.MaxValue)
    val eventSource = EventSourcing.apply[P, T, S, E](eventSourceFn)

    src.scan[(Instance[P, T, S], Event)]((Instance.uninitialized[P, T, S](topology), null.asInstanceOf[Event])) {
      case ((instance, prev), e) ⇒
        val serializedEvent = e.event.asInstanceOf[AnyRef]
        val deserializedEvent = serializer.deserializeEvent(serializedEvent)(instance)
        val updatedInstance = eventSource.apply(instance)(deserializedEvent)
        (updatedInstance, deserializedEvent)
    }.drop(1) // Just to drop the first event 'uninitialized', not interesting for the consumers.
  }

  def allProcessIds(processType: String, readJournal: PersistenceIdsQuery)(implicit actorSystem: ActorSystem): Source[String, NotUsed] = {
    readJournal.persistenceIds()
      .map(id ⇒ ProcessInstance.persistenceId2ProcessId(processType, id)) // This filters out anything that is not a processId (like shard actors, any other actors)
      .collect {
        case Some(processId) ⇒ processId
      }
  }

  def currentProcessIds(processType: String, readJournal: CurrentPersistenceIdsQuery)(implicit actorSystem: ActorSystem): Source[String, NotUsed] = {
    readJournal.currentPersistenceIds()
      .map(id ⇒ ProcessInstance.persistenceId2ProcessId(processType, id)) // This filters out anything that is not a processId (like shard actors, any other actors)
      .collect {
        case Some(processId) ⇒ processId
      }
  }
}