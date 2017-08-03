package com.ing.baker.runtime.actor

import akka.actor.{ActorLogging, ActorRef, Props, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol.{AlreadyInitialized, FireTransition, GetState, Initialize, Uninitialized}

import scala.collection.mutable
import ActorIndex._
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol

import scala.concurrent.duration.Duration

object ActorIndex {

  def props(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String) = Props(new ActorIndex(petriNetActorProps, recipeMetadata))

  case class ActorMetadata(id: String, createdDateTime: Long)

  // when an actor is created
  case class ActorCreated(processId: String, createdDateTime: Long) extends InternalBakerEvent

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends InternalBakerEvent

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends InternalBakerEvent

  /**
    * Indicates that a process can no longer receive events because the configured period has expired.
    */
  case object ReceivePeriodExpired extends InternalBakerMessage

}

class ActorIndex(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, receivePeriod: Duration = Duration.Undefined) extends PersistentActor with ActorLogging {

  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()

  private[actor] def createChildPetriNetActor(id: String) = {
    val actorRef = context.actorOf(petriNetActorProps, name = id)
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

      context.child(id) match {
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

      def forwardIfWithinPeriod(actorRef: ActorRef, msg: PetriNetInstanceProtocol.Command) = {
        if (receivePeriod.isFinite() && cmd.isInstanceOf[FireTransition]) {
          index.get(id).foreach { p =>
            if (System.currentTimeMillis() - p.createdDateTime > receivePeriod.toMillis) {
              sender() ! ReceivePeriodExpired
            }
            else
              actorRef.forward(cmd)
          }
        }
        else
          actorRef.forward(cmd)
      }

      context.child(id) match {
        case Some(actorRef) =>
           forwardIfWithinPeriod(actorRef, cmd)
        case None if index.contains(id) =>
          persist(ActorActivated(id)) { _ =>
            forwardIfWithinPeriod(createChildPetriNetActor(id), cmd)
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
