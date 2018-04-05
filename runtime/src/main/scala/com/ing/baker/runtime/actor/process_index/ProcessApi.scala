package com.ing.baker.runtime.actor.process_index

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props, ReceiveTimeout}
import akka.stream.scaladsl.{Source, SourceQueueWithComplete}
import akka.stream.{Materializer, OverflowStrategy}
import akka.util.Timeout
import com.ing.baker.petrinet.runtime.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.core.events
import com.ing.baker.runtime.core.events.RejectReason

import scala.concurrent.duration.FiniteDuration

/**
 * An actor that pushes all received messages on a SourceQueueWithComplete.
 */
class QueuePushingActor(cmd: ProcessEvent, queue: SourceQueueWithComplete[Any], waitForRetries: Boolean)(implicit timeout: FiniteDuration, system: ActorSystem) extends Actor {
  var runningJobs = Set.empty[Long]

  context.setReceiveTimeout(timeout)

  def completeWith(msg: Any) = {
    queue.offer(msg)
    queue.complete()
    stopActor()
  }

  def rejectedWith(msg: Any, rejectReason: RejectReason) = {
    system.eventStream.publish(events.EventRejected(System.currentTimeMillis(), cmd.processId, cmd.correlationId, cmd.event, rejectReason))
    completeWith(msg)
  }

  override def receive: Receive = {
    case msg: ReceivePeriodExpired ⇒
      rejectedWith(msg, events.ReceivePeriodExpired)

    case msg: InvalidEvent =>
      rejectedWith(msg, events.InvalidEvent)

    case msg: ProcessDeleted =>
      rejectedWith(msg, events.ProcessDeleted)

    case msg: TransitionNotEnabled =>
      rejectedWith(msg, events.FiringLimitMet)

    case msg: AlreadyReceived ⇒
      rejectedWith(msg, events.AlreadReceived)

    case msg @ (_: ProcessUninitialized | _: Uninitialized) =>
      rejectedWith(msg, events.NoSuchProcess)

    //Messages from the ProcessInstances
    case e: TransitionFired ⇒
      queue.offer(e)

      runningJobs = runningJobs ++ e.newJobsIds - e.jobId

      stopActorIfDone

    case msg @ TransitionFailed(_, _, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
      queue.offer(msg)

    case msg @ TransitionFailed(jobId, _,  _, _, _, _, _) ⇒
      runningJobs = runningJobs - jobId
      queue.offer(msg)
      stopActorIfDone

    //Akka default cases
    case ReceiveTimeout ⇒
      queue.fail(new TimeoutException(s"Timeout, no message received in: $timeout"))
      stopActor()

    case msg @ _ ⇒
      queue.fail(new IllegalStateException(s"Unexpected message: $msg"))
      stopActor()
  }

  def stopActor() = context.stop(self)

  def stopActorIfDone: Unit =
    if (runningJobs.isEmpty) {
      queue.complete()
      stopActor()
    }
}

/**
 * Contains some methods to interact with a process instance actor.
 */
class ProcessApi(actor: ActorRef)(implicit actorSystem: ActorSystem, materializer: Materializer) {

  /**
   * Returns a Source of all the messages from a petri net actor in response to a message.
   */
  def askAndCollectAll(cmd: ProcessEvent, waitForRetries: Boolean = false)(implicit timeout: Timeout): Source[Any, NotUsed] =
    Source.queue[Any](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      val sender = actorSystem.actorOf(Props(new QueuePushingActor(cmd, queue, waitForRetries)(timeout.duration, actorSystem)))
      actor.tell(cmd, sender)
      NotUsed.getInstance()
    }
}
