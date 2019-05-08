package com.ing.baker.runtime.core.actor.process_index

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props, ReceiveTimeout}
import akka.stream.scaladsl.{Source, SourceQueueWithComplete}
import akka.stream.{Materializer, OverflowStrategy}
import akka.util.Timeout
import com.ing.baker.runtime.core.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.core.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.core.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.core.actor.serialization.BakerSerializable
import com.ing.baker.runtime.core.events.RejectReason
import org.slf4j.LoggerFactory

import scala.concurrent.duration.FiniteDuration

object ProcessEventReceiver {

  case class InitializeProcessEventReceiver(queue: SourceQueueWithComplete[Any])

  case class ProcessEventRejected(message: String) extends BakerSerializable

  /**
    * Returns a Source of all the messages from a process instance in response to a message.
    */
  def apply(waitForRetries: Boolean = false)(implicit timeout: FiniteDuration, actorSystem: ActorSystem, materializer: Materializer): (Source[Any, NotUsed], ActorRef) = {
    val receiver = actorSystem.actorOf(Props(new ProcessEventReceiver(waitForRetries)(timeout, actorSystem)))
    implicit val akkaTimeout: Timeout = timeout
    val source = Source.queue[Any](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      receiver ! InitializeProcessEventReceiver(queue)
      NotUsed.getInstance()
    }
    (source, receiver)
  }
}

/**
  * An actor that pushes all received messages on a SourceQueueWithComplete.
  */
class ProcessEventReceiver(waitForRetries: Boolean)(implicit timeout: FiniteDuration, system: ActorSystem) extends Actor {

  /** Cache used for storing messages which arrive before initialization */
  var cache = List.empty[Any]
  var runningJobs = Set.empty[Long]

  context.setReceiveTimeout(timeout)

  private val log = LoggerFactory.getLogger(classOf[ProcessEventReceiver])

  def receive: Receive = {

    case ProcessEventReceiver.InitializeProcessEventReceiver(queue) =>
      val initf = initialized(queue)
      cache.reverse.foreach(initf.apply)
      context.become(initf)

    case msg =>
      log.debug(s"Have to cache $msg because arrived before initialization of ProcessEventReceiver")
      cache = msg :: cache
  }

  def initialized(queue: SourceQueueWithComplete[Any]): Receive = {

    def stopActorIfDone(): Unit =
      if (runningJobs.isEmpty) {
        log.debug("Stopping ProcessEventReceiver and completing queue")
        queue.complete()
        stopActor()
      }

    def completeWith(msg: Any) = {
      queue.offer(msg)
      log.debug("Stopping ProcessEventReceiver and completing queue")
      queue.complete()
      stopActor()
    }

    def rejectedWith(msg: Any, rejectReason: RejectReason) = {
      log.debug("Stopping ProcessEventReceiver and rejecting queue")
      log.debug("Reject reason: " + rejectReason)
      log.debug("message: " + msg)
      completeWith(msg)
    }

    {
      case msg: TransitionNotEnabled =>
        rejectedWith(msg, RejectReason.FiringLimitMet)

      case msg: AlreadyReceived ⇒
        rejectedWith(msg, RejectReason.AlreadyReceived)

      case msg: Uninitialized ⇒
        rejectedWith(msg, RejectReason.NoSuchProcess)

      //Messages from the ProcessInstances
      case e: TransitionFired ⇒
        queue.offer(e)

        runningJobs = runningJobs ++ e.newJobsIds - e.jobId

        stopActorIfDone()

      case msg@TransitionFailed(_, _, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
        queue.offer(msg)

      case msg@TransitionFailed(jobId, _, _, _, _, _, _) ⇒
        runningJobs = runningJobs - jobId
        queue.offer(msg)
        stopActorIfDone()

      // Rejections
      case msg: ReceivePeriodExpired =>
        rejectedWith(msg, RejectReason.ReceivePeriodExpired)

      case msg: InvalidEvent =>
        rejectedWith(msg, RejectReason.InvalidEvent)

      case msg: ProcessDeleted =>
        rejectedWith(msg, RejectReason.ProcessDeleted)

      case msg: NoSuchProcess =>
        rejectedWith(msg, RejectReason.NoSuchProcess)

      //Akka default cases
      case ReceiveTimeout ⇒
        log.debug("Timeout on ProcessEventReceiver")
        queue.fail(new TimeoutException(s"Timeout, no message received in: $timeout"))
        stopActor()

      case msg@_ ⇒
        log.debug("Unexpected message on ProcessEventReceiver")
        queue.fail(new IllegalStateException(s"Unexpected message: $msg"))
        stopActor()
    }
  }

  def stopActor() = {
    log.debug("Stopping the ProcessEventReceiver")
    context.stop(self)
  }
}
