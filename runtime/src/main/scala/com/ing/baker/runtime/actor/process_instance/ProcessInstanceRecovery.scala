package com.ing.baker.runtime.actor.process_instance

import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.serialization.SerializationExtension
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing._
import com.ing.baker.petrinet.runtime.{EventSourcing, Instance}
import com.ing.baker.runtime.actor.serialization.{Encryption, ProtoEventAdapterImpl}

abstract class ProcessInstanceRecovery[P : Identifiable, T : Identifiable, S, E](
     val topology: PetriNet[P, T],
     encryption: Encryption,
     eventSourceFn: T => (S => E => S)) extends PersistentActor {

  implicit val system = context.system

  val eventSource = EventSourcing.apply[P, T, S, E](eventSourceFn)

  private val protoEventAdapter = new ProtoEventAdapterImpl(SerializationExtension.get(system), encryption)
  private val serializer = new ProcessInstanceSerialization[P, T, S, E](protoEventAdapter)

  def onRecoveryCompleted(state: Instance[P, T, S])

  def persistEvent[O](instance: Instance[P, T, S], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    persist(serializedEvent) { persisted => fn(e) }
  }

  private var recoveringState: Instance[P, T, S] = Instance.uninitialized[P, T, S](topology)

  private def applyToRecoveringState(e: AnyRef) = {
    val deserializedEvent = serializer.deserializeEvent(e)(recoveringState)
    recoveringState = eventSource(recoveringState)(deserializedEvent)
  }

  override def receiveRecover: Receive = {
    case e: protobuf.Initialized      ⇒ applyToRecoveringState(e)
    case e: protobuf.TransitionFired  ⇒ applyToRecoveringState(e)
    case e: protobuf.TransitionFailed ⇒ applyToRecoveringState(e)
    case RecoveryCompleted ⇒
      if (recoveringState.sequenceNr > 0)
        onRecoveryCompleted(recoveringState)
  }
}
