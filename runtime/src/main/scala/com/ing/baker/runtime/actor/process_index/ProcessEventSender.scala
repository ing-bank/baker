package com.ing.baker.runtime.actor.process_index

import akka.actor.{Actor, ActorRef, Props, ReceiveTimeout}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol.ProcessEvent
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.core.events.{EventReceived, EventRejected, RejectReason}
import org.slf4j.LoggerFactory

import scala.concurrent.duration.FiniteDuration

object ProcessEventSender {

  def apply(receiver: ActorRef, cmd: ProcessEvent, recipe: CompiledRecipe, waitForRetries: Boolean)(implicit timeout: FiniteDuration): Props =
    Props(new ProcessEventSender(receiver, cmd, recipe, waitForRetries))
}

/**
  * An actor that pushes all received messages on the process instance side to the node which requested a process event operation.
  * It's main usage is the publishing of events to the system event stream and logging message throughput.
  */
class ProcessEventSender(receiver: ActorRef, cmd: ProcessEvent, recipe: CompiledRecipe, waitForRetries: Boolean)(implicit timeout: FiniteDuration) extends Actor {

  var runningJobs = Set.empty[Long]

  var firstReceived = false

  context.setReceiveTimeout(timeout)

  private val log = LoggerFactory.getLogger(classOf[ProcessEventSender])

  def stopActorIfDone(): Unit =
    if (runningJobs.isEmpty) {
      log.debug("Stopping ProcessEventSender")
      stopActor()
    }

  def completeWith(msg: Any) = {
    receiver ! msg
    log.debug("Stopping ProcessEventSender")
    stopActor()
  }

  def rejectedWith(msg: Any, rejectReason: RejectReason) = {
    context.system.eventStream.publish(EventRejected(System.currentTimeMillis(), cmd.processId, cmd.correlationId, cmd.event, rejectReason))
    log.debug("Stopping ProcessEventSender and rejecting queue")
    log.debug("Reject reason: " + rejectReason)
    log.debug("message: " + msg)
    completeWith(msg)
  }

  def stopActor() = {
    log.debug("Stopping the ProcessEventSender")
    context.stop(self)
  }

  def receive: Receive = {

    case msg: TransitionNotEnabled =>
      rejectedWith(msg, RejectReason.FiringLimitMet)

    case msg: AlreadyReceived ⇒
      rejectedWith(msg, RejectReason.AlreadyReceived)

    case msg: Uninitialized ⇒
      rejectedWith(msg, RejectReason.NoSuchProcess)

    //Messages from the ProcessInstances
    case e: TransitionFired ⇒
      receiver ! e

      if (!firstReceived)
        context.system.eventStream.publish(EventReceived(System.currentTimeMillis(), recipe.name, recipe.recipeId, cmd.processId, cmd.correlationId, cmd.event))

      firstReceived = true

      runningJobs = runningJobs ++ e.newJobsIds - e.jobId

      stopActorIfDone()

    case msg@TransitionFailed(_, _, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
      receiver ! msg

    case msg@TransitionFailed(jobId, _, _, _, _, _, _) ⇒
      runningJobs = runningJobs - jobId
      receiver ! msg
      stopActorIfDone()

    //Akka default cases
    case ReceiveTimeout ⇒
      log.debug("Timeout on ProcessEventSender")
      stopActor()

    case msg@_ ⇒
      log.debug("Unexpected message on ProcessEventSender")
      receiver ! msg
      stopActor()
  }
}

