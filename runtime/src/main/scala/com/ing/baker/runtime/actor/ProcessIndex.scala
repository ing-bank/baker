package com.ing.baker.runtime.actor

import akka.actor.{ActorLogging, ActorRef, Props, SupervisorStrategy, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import PetriNetInstanceProtocol._
import com.ing.baker.runtime.actor.ProcessIndex._

import scala.collection.mutable
import scala.concurrent.duration._


object ProcessIndex {

  def props(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String, receivePeriod: Duration, retentionPeriod: Duration) =
    Props(new ProcessIndex(petriNetActorProps, recipeMetadata, receivePeriod, retentionPeriod))

  case class ActorMetadata(id: String, createdDateTime: Long)

  // when an actor is created
  case class ActorCreated(processId: String, createdDateTime: Long) extends InternalBakerEvent

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends InternalBakerEvent

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends InternalBakerEvent

  // when an actor is deleted
  case class ActorDeleted(processId: String) extends InternalBakerEvent

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

  import context.dispatcher

  if (retentionPeriod.isFinite())
    context.system.scheduler.schedule(cleanupInterval, cleanupInterval, context.self, CheckForProcessesToBeDeleted)

  private[actor] def getOrCreateProcessActor(id: String): ActorRef = {
    val actorRef = context.actorOf(processActorProps, name = id)
    context.watch(actorRef)
    actorRef
  }

  def shouldDelete(meta: ActorMetadata) = meta.createdDateTime + cleanupInterval.toMillis < System.currentTimeMillis()

  def deleteProcess(processId: String) = {
    persist(ActorDeleted(processId)) { _ =>
      val meta = index(processId)
      recipeMetadata.remove(ProcessMetadata(meta.id, meta.createdDateTime))
      index -= processId
    }
  }

  override def receiveCommand: Receive = {
    case CheckForProcessesToBeDeleted =>
      val toBeDeleted = index.values.filter(shouldDelete)
      log.debug(s"Deleting processes: {}", toBeDeleted.mkString(","))
      toBeDeleted.foreach(meta => getOrCreateProcessActor(meta.id) ! Stop(delete = true))

    case Passivate(stopMessage) =>
      sender() ! stopMessage

    case Terminated(actorRef) =>
      val processId = actorRef.path.name

      index.get(processId) match {
        case Some(meta) if shouldDelete(meta) =>
          deleteProcess(processId)
        case Some(_) =>
          persist(ActorPassivated(processId)) { _ => }
        case None =>
          log.warning(s"Received Terminated message for non indexed actor: $actorRef")
      }

    case BakerActorMessage(processId, cmd@Initialize(_, _)) =>

      val id = processId.toString

      context.child(id) match {
        case None if !index.contains(id) =>
          val created = System.currentTimeMillis()
          persist(ActorCreated(id, created)) { _ =>
            getOrCreateProcessActor(id).forward(cmd)
            val actorMetadata = ActorMetadata(id, created)
            index += id -> actorMetadata
            recipeMetadata.add(ProcessMetadata(id, created))
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
            forwardIfWithinPeriod(getOrCreateProcessActor(id), cmd)
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
      actorsToBeCreated += processId
    case ActorPassivated(processId) =>
      actorsToBeCreated -= processId
    case ActorActivated(processId) =>
      actorsToBeCreated += processId
    case ActorDeleted(processId) =>
      actorsToBeCreated -= processId
      index -= processId
    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => getOrCreateProcessActor(id))
      index.values.foreach(p => recipeMetadata.add(ProcessMetadata(p.id, p.createdDateTime)))
  }

  override def persistenceId: String = self.path.name
}
