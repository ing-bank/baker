package com.ing.baker.runtime.actor.process_index

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props, ReceiveTimeout}
import akka.stream.scaladsl.{Source, SourceQueueWithComplete}
import akka.stream.{Materializer, OverflowStrategy}
import akka.util.Timeout
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.serialization.BakerSerializable
import com.ing.baker.runtime.core.events.RejectReason
import org.slf4j.LoggerFactory

import scala.concurrent.duration.FiniteDuration

object ProcessEventActor {

  case class Initialize(queue: SourceQueueWithComplete[Any])

  //case class ProcessEventRejected(message: String) extends BakerSerializable

  /**
    * Returns a Source of all the messages from a process instance in response to a message.
    */
  def apply(/*processInstance: ActorRef, recipe: CompiledRecipe, cmd: ProcessEvent, */ waitForRetries: Boolean = false)
           (implicit timeout: FiniteDuration, actorSystem: ActorSystem, materializer: Materializer): (Source[Any, NotUsed], ActorRef) = {
    val receiver = actorSystem.actorOf(Props(new ProcessEventActor(/*cmd, recipe,queue,*/ waitForRetries)(timeout, actorSystem)))
    implicit val akkaTimeout: Timeout = timeout
    val source = Source.queue[Any](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      receiver ! Initialize(queue)
      //TODO move this validation to the process index
      /*
      require(cmd.event != null, "Event can not be null")

      //TODO translate this error to an actor message for ProcessEventActor
      val t: Transition = recipe.petriNet.transitions.find(_.label == cmd.event.name).getOrElse {
        throw new IllegalArgumentException(s"No such event known in recipe: ${cmd.event.name}")
      }
      */

      //TODO move to process index
      //val fireTransitionCmd = FireTransition(t.id, cmd.event, cmd.correlationId)

      // TODO make this redirect on process index
      //processInstance.tell(fireTransitionCmd, sender)
      NotUsed.getInstance()
    }
    (source, receiver)
  }
}

/**
  * An actor that pushes all received messages on a SourceQueueWithComplete.
  */
class ProcessEventActor(/*cmd: ProcessEvent, recipe: CompiledRecipe,*/ waitForRetries: Boolean)(implicit timeout: FiniteDuration, system: ActorSystem) extends Actor {
  var runningJobs = Set.empty[Long]
  //TODO Move event stream publishing to process instance
  //var firstReceived = false

  context.setReceiveTimeout(timeout)

  private val log = LoggerFactory.getLogger(classOf[ProcessEventActor])

  def receive: Receive = {

    case ProcessEventActor.Initialize(queue) => context.become(initialized(queue))
  }

  def initialized(queue: SourceQueueWithComplete[Any]): Receive = {

    def stopActorIfDone(): Unit =
      if (runningJobs.isEmpty) {
        log.debug("Stopping ProcessEventActor and completing queue")
        queue.complete()
        stopActor()
      }

    def completeWith(msg: Any) = {
      queue.offer(msg)
      log.debug("Stopping ProcessEventActor and completing queue")
      queue.complete()
      stopActor()
    }

    def rejectedWith(msg: Any, rejectReason: RejectReason) = {
      //TODO Move event stream publishing to process instance
      //system.eventStream.publish(events.EventRejected(System.currentTimeMillis(), cmd.processId, cmd.correlationId, cmd.event, rejectReason))
      log.debug("Stopping ProcessEventActor and rejecting queue")
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

        //TODO Move event stream publishing to process instance
        /*
        if (!firstReceived)
          system.eventStream.publish(events.EventReceived(System.currentTimeMillis(), recipe.name, recipe.recipeId, cmd.processId, cmd.correlationId, cmd.event))

        firstReceived = true
        */

        runningJobs = runningJobs ++ e.newJobsIds - e.jobId

        stopActorIfDone()

      case msg@TransitionFailed(_, _, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
        queue.offer(msg)

      case msg@TransitionFailed(jobId, _, _, _, _, _, _) ⇒
        runningJobs = runningJobs - jobId
        queue.offer(msg)
        stopActorIfDone()

      //Akka default cases
      case ReceiveTimeout ⇒
        log.debug("Timeout on ProcessEventActor")
        queue.fail(new TimeoutException(s"Timeout, no message received in: $timeout"))
        stopActor()

      case msg@_ ⇒
        log.debug("Unexpected message on ProcessEventActor")
        queue.fail(new IllegalStateException(s"Unexpected message: $msg"))
        stopActor()
    }
  }

  def stopActor() = {
    log.debug("Stopping the ProcessEventActor")
    context.stop(self)
  }
}
