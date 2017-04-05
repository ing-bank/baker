package com.ing.baker.actor

import akka.actor.{ActorLogging, ActorRef, Props, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import io.kagera.akka.actor.PetriNetInstanceProtocol.{AlreadyInitialized, Initialize, Uninitialized}

import scala.collection.mutable
import ActorIndex._

object ActorIndex {

  def props(petriNetActorProps: Props) = Props(new ActorIndex(petriNetActorProps))

  case class ActorCreated(processId: String) extends InternalBakerEvent

  case class ActorTerminated(processId: String) extends InternalBakerEvent

  case object GetActorIndex extends InternalBakerMessage

}

class ActorIndex(petriNetActorProps: Props) extends PersistentActor with ActorLogging {

  private val runningActors: mutable.Map[String, ActorRef] = mutable.Map[String, ActorRef]()
  private val passivated: mutable.Set[String] = mutable.Set.empty

  private def createActor(id: String) = {
    val actorRef = context.actorOf(petriNetActorProps, name = id)
    context.watch(actorRef)
    runningActors.put(id, actorRef)
    actorRef
  }

  override def receiveCommand: Receive = {
    case Passivate(stopMessage) =>
      sender() ! stopMessage

    case Terminated(actorRef) =>
      val id = actorRef.path.name
      persist(ActorTerminated(id)) { _ =>
        passivated += id
        runningActors -= id
      }

    case BakerActorMessage(processId, cmd@Initialize(_, _)) =>

      val id = processId.toString

      runningActors.get(id) match {
        case None if !passivated.contains(id) =>
          persist(ActorCreated(id)) { _ =>
            createActor(id).forward(cmd)
          }
        case _ => sender() ! AlreadyInitialized
      }

    case BakerActorMessage(processId, cmd) =>

      val id = processId.toString

      runningActors.get(id) match {
        case Some(actorRef) => actorRef.forward(cmd)
        case _ if passivated.contains(id) =>
          persist(ActorCreated(id)) { _ =>
            createActor(id).forward(cmd)
            passivated -= id
          }
        case _ => sender() ! Uninitialized(processId.toString)
      }

    case GetActorIndex => (runningActors.keys ++ passivated).toSet

    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  private val recoveringIds: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(processId) =>
      recoveringIds += processId
      passivated -= processId
    case ActorTerminated(processId) =>
      recoveringIds -= processId
      passivated += processId
    case RecoveryCompleted =>
      (recoveringIds -- passivated).foreach(id => runningActors += id -> createActor(id))
  }

  override def persistenceId: String = self.path.name
}
