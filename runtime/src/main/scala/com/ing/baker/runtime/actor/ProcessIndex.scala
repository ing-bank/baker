package com.ing.baker.runtime.actor

import akka.actor.{ActorLogging, ActorRef, Props, Terminated}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.runtime.actor.PetriNetInstanceProtocol._
import com.ing.baker.runtime.actor.ProcessIndex._

import scala.collection.mutable
import scala.concurrent.duration._


object ProcessIndex {

  def props(petriNetActorProps: Props, recipeMetadata: RecipeMetadata, recipeName: String, receivePeriod: Duration, retentionPeriod: Duration, retentionCheckInterval: FiniteDuration) =
    Props(new ProcessIndex(petriNetActorProps, recipeMetadata, receivePeriod, retentionPeriod, retentionCheckInterval))

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

  def getOrCreateProcessActor(processId: String): ActorRef =
    context.child(processId).getOrElse(createProcessActor(processId))

  def createProcessActor(processId: String): ActorRef = {
    val processActor = context.actorOf(processActorProps, name = processId)
    context.watch(processActor)
    processActor
  }

  def shouldDelete(meta: ActorMetadata): Boolean = meta.createdDateTime + retentionPeriod.toMillis < System.currentTimeMillis()

  def deleteProcess(processId: String): Unit = {
    persist(ActorDeleted(processId)) { _ =>
      val meta = index(processId)
      recipeMetadata.remove(ProcessMetadata(meta.id, meta.createdDateTime))
      index -= processId
    }
  }

  override def receiveCommand: Receive = {
    case CheckForProcessesToBeDeleted =>
      val toBeDeleted = index.values.filter(shouldDelete)
      if (toBeDeleted.nonEmpty)
        log.debug(s"Deleting processes: {}", toBeDeleted.mkString(","))

      toBeDeleted.foreach(meta => getOrCreateProcessActor(meta.id) ! Stop(delete = true))

    case Passivate(stopMessage) =>
      sender() ! stopMessage

    case Terminated(actorRef) =>
      val processId = actorRef.path.name
      log.debug(s"Actor terminated: $actorRef")

      index.get(processId) match {
        case Some(meta) if shouldDelete(meta) =>
          deleteProcess(processId)
        case Some(_) =>
          persist(ActorPassivated(processId)) { _ => }
        case None =>
          log.warning(s"Received Terminated message for non indexed actor: $actorRef")
      }

    case BakerActorMessage(processId, cmd@Initialize(_, _)) =>

      context.child(processId) match {
        case None if !index.contains(processId) =>
          val created = System.currentTimeMillis()
          persist(ActorCreated(processId, created)) { _ =>
            createProcessActor(processId).forward(cmd)
            val actorMetadata = ActorMetadata(processId, created)
            index += processId -> actorMetadata
            recipeMetadata.add(ProcessMetadata(processId, created))
          }
        case _ => sender() ! AlreadyInitialized
      }

    case BakerActorMessage(processId, cmd) =>

      def forwardIfWithinPeriod(actorRef: ActorRef, msg: PetriNetInstanceProtocol.Command) = {
        if (receivePeriod.isFinite() && cmd.isInstanceOf[FireTransition]) {
          index.get(processId).foreach { p =>
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

      context.child(processId) match {
        case Some(actorRef) =>
           forwardIfWithinPeriod(actorRef, cmd)
        case None if index.contains(processId) =>
          persist(ActorActivated(processId)) { _ =>
            forwardIfWithinPeriod(createProcessActor(processId), cmd)
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
      actorsToBeCreated.foreach(id => createProcessActor(id))
      index.values.foreach(p => recipeMetadata.add(ProcessMetadata(p.id, p.createdDateTime)))
  }

  override def persistenceId: String = self.path.name
}
