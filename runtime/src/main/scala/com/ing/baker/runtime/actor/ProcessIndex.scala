package com.ing.baker.runtime.actor

import akka.actor.{ActorLogging, ActorRef, Props, SupervisorStrategy, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol._
import com.ing.baker.runtime.actor.ProcessIndex._

import scala.collection.mutable
import scala.concurrent.duration._


object ProcessIndex {

  def props(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String, receivePeriod: Duration) = Props(new ProcessIndex(petriNetActorProps, recipeMetadata, receivePeriod))

  case class ActorMetadata(id: String, createdDateTime: Long)

  // when an actor is created
  case class ActorCreated(processId: String, createdDateTime: Long) extends InternalBakerEvent

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends InternalBakerEvent

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends InternalBakerEvent

  // when an actor is deleted
  case class ActorDeleted(processId: String) extends InternalBakerEvent


  case class DeleteProcess(processId: String) extends InternalBakerMessage


  case object CheckForProcessesToBeDeleted extends InternalBakerMessage

  /**
    * Indicates that a process can no longer receive events because the configured period has expired.
    */
  case object ReceivePeriodExpired extends InternalBakerMessage

}

class ProcessIndex(processActorProps: Props,
                   recipeMetadata: RecipeMetadata,
                   receivePeriod: Duration = Duration.Undefined,
                   retentionPeriod: Duration = Duration.Undefined,
                   cleanupInterval: FiniteDuration = 1 minute) extends PersistentActor with ActorLogging {

  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()

  if (retentionPeriod.isFinite())
    context.system.scheduler.schedule(cleanupInterval, cleanupInterval, context.self, CheckForProcessesToBeDeleted)

  private[actor] def createProcessActor(id: String) = {
    val actorRef = context.actorOf(processActorProps, name = id)
    context.watch(actorRef)
    actorRef
  }

  def shouldDelete(meta: ActorMetadata) = meta.createdDateTime + cleanupInterval.toMillis < System.currentTimeMillis()

  override def receiveCommand: Receive = {
    case CheckForProcessesToBeDeleted =>
      index.values
        .filter(_.createdDateTime + cleanupInterval.toMillis < System.currentTimeMillis())
        .foreach { meta =>

          val processId = meta.id

          // if there is a child (living process) we first stop it
          context.child(processId).foreach(actor =>
            actor ! SupervisorStrategy.Stop
          )

          // otherwise directly remove it from the index
          if(!context.child(processId).isDefined)
            persist(ActorDeleted(processId)) { _ => index -= processId }
        }

    case Passivate(stopMessage) =>
      sender() ! stopMessage

    case Terminated(actorRef) =>
      val processId = actorRef.path.name

      if(shouldDelete(index(processId)))
        persist(ActorDeleted(processId)) { _ => index -= processId }
      else
        persist(ActorPassivated(processId)) { _ => }

    case BakerActorMessage(processId, cmd@Initialize(_, _)) =>

      val id = processId.toString

      context.child(id) match {
        case None if !index.contains(id) =>
          val created = System.currentTimeMillis()
          persist(ActorCreated(id, created)) { _ =>
            createProcessActor(id).forward(cmd)
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
            forwardIfWithinPeriod(createProcessActor(id), cmd)
          }
        case None => sender() ! Uninitialized(processId.toString)
      }

    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  // This Set holds all the actor ids to be created again after the recovery completed
  private val actorsToBeCreated: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(processId, createdTime) =>
      index += processId -> ActorMetadata(processId, createdTime)
      recipeMetadata.addNewProcessMetadata(processId, createdTime)
      actorsToBeCreated += processId
    case ActorPassivated(processId) =>
      actorsToBeCreated -= processId
    case ActorActivated(processId) =>
      actorsToBeCreated += processId
    case ActorDeleted(processId) =>
      actorsToBeCreated -= processId
      index -= processId
    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createProcessActor(id))
  }

  override def persistenceId: String = self.path.name
}
