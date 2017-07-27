package io.kagera.akka.actor

import akka.NotUsed
import akka.actor.{ Actor, ActorRef, ActorSystem, Props, ReceiveTimeout }
import akka.stream.scaladsl.{ Sink, Source, SourceQueueWithComplete }
import akka.stream.{ Materializer, OverflowStrategy }
import akka.util.Timeout
import akka.pattern._
import io.kagera.akka.actor.PetriNetInstanceProtocol._
import io.kagera.api.PetriNet
import io.kagera.runtime.ExceptionStrategy.RetryWithDelay
import io.kagera.dsl.colored._

import scala.collection.immutable.Seq
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ Await, Future }

/**
 * An actor that pushes all received messages on a SourceQueueWithComplete.
 */
class QueuePushingActor(queue: SourceQueueWithComplete[TransitionResponse], waitForRetries: Boolean)(implicit timeout: FiniteDuration) extends Actor {
  var runningJobs = Set.empty[Long]

  context.setReceiveTimeout(timeout)

  override def receive: Receive = {
    case e: TransitionFired ⇒
      queue.offer(e)

      runningJobs = runningJobs ++ e.newJobsIds - e.jobId

      stopActorIfDone

    case msg @ TransitionFailed(_, _, _, _, _, RetryWithDelay(_)) if waitForRetries ⇒
      queue.offer(msg)

    case msg @ TransitionFailed(jobId, _, _, _, _, _) ⇒
      runningJobs = runningJobs - jobId
      queue.offer(msg)
      stopActorIfDone

    case Uninitialized(id) ⇒
      completeQueueAndStop()

    case msg @ TransitionNotEnabled(id, reason) ⇒
      queue.offer(msg)
      completeQueueAndStop()

    case ReceiveTimeout ⇒
      queue.fail(new IllegalStateException(s"Timeout, no message received in: $timeout"))
      completeQueueAndStop()

    case msg @ _ ⇒
      queue.fail(new IllegalStateException(s"Unexpected message: $msg"))
      completeQueueAndStop()
  }

  def completeQueueAndStop() = {
    queue.complete()
    context.stop(self)
  }

  def stopActorIfDone: Unit =
    if (runningJobs.isEmpty)
      completeQueueAndStop()
}

/**
 * Contains some methods to interact with a petri net instance actor.
 */
class PetriNetInstanceApi[P[_], T[_, _], S](topology: PetriNet[P[_], T[_, _]], actor: ActorRef)(implicit actorSystem: ActorSystem, materializer: Materializer) {

  /**
   * Fires a transition and confirms (waits) for the result of that transition firing.
   */
  def askAndConfirmFirst[S](msg: Any)(implicit timeout: Timeout): Future[TransitionResponse] = actor.ask(msg).mapTo[TransitionResponse]

  /**
   * Synchronously collects all messages in response to a message sent to a PetriNet instance.
   */
  def askAndCollectAllSync(msg: Any, waitForRetries: Boolean = false)(implicit timeout: Timeout): Seq[TransitionResponse] = {
    val futureResult = askAndCollectAll(msg, waitForRetries).runWith(Sink.seq)
    Await.result(futureResult, timeout.duration)
  }

  /**
   * Sends a FireTransition command to the actor and returns a Source of TransitionResponse messages
   */
  def fireTransition(transitionId: Long, input: Any)(implicit timeout: Timeout): Source[TransitionResponse, NotUsed] =
    askAndCollectAll(FireTransition(transitionId, input))

  /**
   * Returns a Source of all the messages from a petri net actor in response to a message.
   *
   */
  def askAndCollectAll(msg: Any, waitForRetries: Boolean = false)(implicit timeout: Timeout): Source[TransitionResponse, NotUsed] =
    Source.queue[TransitionResponse](100, OverflowStrategy.fail).mapMaterializedValue { queue ⇒
      val sender = actorSystem.actorOf(Props(new QueuePushingActor(queue, waitForRetries)(timeout.duration)))
      actor.tell(msg, sender)
      NotUsed.getInstance()
    }
}
