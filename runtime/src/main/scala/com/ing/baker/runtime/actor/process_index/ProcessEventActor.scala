package com.ing.baker.runtime.actor.process_index

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props, ReceiveTimeout}
import akka.stream.scaladsl.{Source, SourceQueueWithComplete}
import akka.stream.{Materializer, OverflowStrategy}
import akka.util.Timeout
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.core.events.RejectReason
import com.ing.baker.runtime.core.{RuntimeEvent, events}

import scala.concurrent.duration.FiniteDuration

object ProcessEventActor {

  /**
    * Returns a Source of all the messages from a process instance in response to a message.
    */
  def processEvent(receiver: ActorRef, recipe: CompiledRecipe, cmd: ProcessEvent, waitForRetries: Boolean = false)
                  (implicit timeout: FiniteDuration, actorSystem: ActorSystem, materializer: Materializer): Source[Any, NotUsed] = {

    implicit val akkaTimeout: Timeout = timeout
    Source.queue[Any](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      val sender = actorSystem.actorOf(Props(new ProcessEventActor(cmd, recipe, queue, waitForRetries)(timeout, actorSystem)))

      require(cmd.event != null, "Event can not be null")

      val t: Transition = recipe.petriNet.transitions.find(_.label == cmd.event.name).getOrElse {
        throw new IllegalArgumentException(s"No such event known in recipe: ${cmd.event.name}")
      }

      val fireTransitionCmd = FireTransition(t.id, cmd.event, cmd.correlationId)

      receiver.tell(fireTransitionCmd, sender)
      NotUsed.getInstance()
    }
  }
}

/**
  * An actor that pushes all received messages on a SourceQueueWithComplete.
  */
class ProcessEventActor(cmd: ProcessEvent, recipe: CompiledRecipe, queue: SourceQueueWithComplete[Any], waitForRetries: Boolean)(implicit timeout: FiniteDuration, system: ActorSystem) extends Actor {
  var runningJobs = Set.empty[Long]
  var firstReceived = false

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

    case msg: TransitionNotEnabled =>
      rejectedWith(msg, RejectReason.FiringLimitMet)

    case msg: AlreadyReceived ⇒
      rejectedWith(msg, RejectReason.AlreadyReceived)

    case msg: Uninitialized ⇒
      rejectedWith(msg, RejectReason.NoSuchProcess)

    //Messages from the ProcessInstances
    case e: TransitionFired ⇒
      queue.offer(e)

      if (!firstReceived)
        system.eventStream.publish(events.EventReceived(System.currentTimeMillis(), recipe.name, recipe.recipeId, cmd.processId, cmd.correlationId, cmd.event))

      firstReceived = true

      runningJobs = runningJobs ++ e.newJobsIds - e.jobId

      stopActorIfDone()

    case msg @ TransitionFailed(_, _, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
      queue.offer(msg)

    case msg @ TransitionFailed(jobId, _,  _, _, _, _, _) ⇒
      runningJobs = runningJobs - jobId
      queue.offer(msg)
      stopActorIfDone()

    //Akka default cases
    case ReceiveTimeout ⇒
      queue.fail(new TimeoutException(s"Timeout, no message received in: $timeout"))
      stopActor()

    case msg @ _ ⇒
      queue.fail(new IllegalStateException(s"Unexpected message: $msg"))
      stopActor()
  }

  def stopActor() = context.stop(self)

  def stopActorIfDone(): Unit =
    if (runningJobs.isEmpty) {
      queue.complete()
      stopActor()
    }
}
