package com.ing.baker.runtime.actor

import akka.actor.{ActorLogging, Props, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import io.kagera.akka.actor.PetriNetInstanceProtocol.{AlreadyInitialized, Initialize, Uninitialized}

import scala.collection.mutable
import ActorIndex._

object ActorIndex {

  def props(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String) = Props(new ActorIndex(petriNetActorProps, recipeMetadata, recipeName))

  case class ActorMetadata(id: String, createdDateTime: Long)

  // when an actor is created
  case class ActorCreated(processId: String, createdDateTime: Long) extends InternalBakerEvent

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends InternalBakerEvent

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends InternalBakerEvent

}

class ActorIndex(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String) extends PersistentActor with ActorLogging {

  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()

  def actorName(id: String) = s"$recipeName-$id"
  def processId(actorName: String) = actorName.replace(recipeName, "")

  private[actor] def createChildPetriNetActor(id: String) = {
    val actorRef = context.actorOf(petriNetActorProps, name = actorName(id))
    context.watch(actorRef)
    actorRef
  }

  override def receiveCommand: Receive = {
    case Passivate(stopMessage) =>
      sender() ! stopMessage

    case Terminated(actorRef) =>
      val id = actorRef.path.name
      persist(ActorPassivated(id)) { _ => }

    case BakerActorMessage(processId, cmd@Initialize(_, _)) =>

      val id = processId.toString

      context.child(actorName(id)) match {
        case None if !index.contains(id) =>
          val created = System.currentTimeMillis()
          persist(ActorCreated(id, created)) { _ =>
            createChildPetriNetActor(id).forward(cmd)
            val actorMetadata = ActorMetadata(id, created)
            index += id -> actorMetadata
            recipeMetadata.addNewProcessMetadata(id, created)
          }
        case _ => sender() ! AlreadyInitialized
      }

    case BakerActorMessage(processId, cmd) =>

      val id = processId.toString

      context.child(actorName(id)) match {
        case Some(actorRef) => actorRef.forward(cmd)
        case None if index.contains(id) =>
          persist(ActorActivated(id)) { _ =>
            createChildPetriNetActor(id).forward(cmd)
          }
        case None => sender() ! Uninitialized(processId.toString)
      }

    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  // This Set holds all the actor ids to be created again after the recovery completed
  private val actorsToBeCreated: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(processId, created) =>
      index += processId -> ActorMetadata(processId, created)
      recipeMetadata.addNewProcessMetadata(processId, created)
      actorsToBeCreated += processId
    case ActorPassivated(processId) =>
      actorsToBeCreated -= processId
    case ActorActivated(processId) =>
      actorsToBeCreated += processId
    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createChildPetriNetActor(id))
  }

  override def persistenceId: String = self.path.name
}
