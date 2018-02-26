package com.ing.baker.runtime.actor.process_index

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props, ReceiveTimeout}
import akka.pattern._
import akka.stream.scaladsl.{Sink, Source, SourceQueueWithComplete}
import akka.stream.{Materializer, OverflowStrategy}
import akka.util.Timeout
import com.ing.baker.petrinet.runtime.ExceptionStrategy.RetryWithDelay
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._

import scala.collection.immutable.Seq
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Future}

/**
 * An actor that pushes all received messages on a SourceQueueWithComplete.
 */
class QueuePushingActor(queue: SourceQueueWithComplete[Any], waitForRetries: Boolean)(implicit timeout: FiniteDuration) extends Actor {
  var runningJobs = Set.empty[Long]

  context.setReceiveTimeout(timeout)

  override def receive: Receive = {
    //Messages from the ProcessIndex
    case msg@ (_:ProcessDeleted | _: ProcessUninitialized | _: ReceivePeriodExpired | _: InvalidEvent) ⇒
      queue.offer(msg)
      queue.complete()
      stopActor()

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

    case msg@ (_: TransitionNotEnabled | _: Uninitialized | _: AlreadyReceived) ⇒
      queue.offer(msg)
      queue.complete()
      stopActor()

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
 * Contains some methods to interact with a petri net instance actor.
 */
class ProcessApi(actor: ActorRef)(implicit actorSystem: ActorSystem, materializer: Materializer) {

  /**
   * Fires a transition and confirms (waits) for the result of that transition firing.
   */
  def askAndConfirmFirst(msg: Any)(implicit timeout: Timeout): Future[Any] = actor.ask(msg).mapTo[Any]

  /**
   * Synchronously collects all messages in response to a message sent to a PetriNet instance.
   */
  def askAndCollectAllSync(msg: Any, waitForRetries: Boolean = false)(implicit timeout: Timeout): Seq[Any] = {
    val futureResult = askAndCollectAll(msg, waitForRetries).runWith(Sink.seq)
    Await.result(futureResult, timeout.duration)
  }

  /**
   * Sends a FireTransition command to the actor and returns a Source of TransitionResponse messages
   */
  def fireTransition(transitionId: Long, input: Any)(implicit timeout: Timeout): Source[Any, NotUsed] =
    askAndCollectAll(FireTransition(transitionId, input))

  /**
   * Returns a Source of all the messages from a petri net actor in response to a message.
   *
   */
  def askAndCollectAll(msg: Any, waitForRetries: Boolean = false)(implicit timeout: Timeout): Source[Any, NotUsed] =
    Source.queue[Any](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      val sender = actorSystem.actorOf(Props(new QueuePushingActor(queue, waitForRetries)(timeout.duration)))
      actor.tell(msg, sender)
      NotUsed.getInstance()
    }
}
