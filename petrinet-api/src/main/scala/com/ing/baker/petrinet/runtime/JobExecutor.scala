package com.ing.baker.petrinet.runtime

import java.io.{PrintWriter, StringWriter}

import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing._
import org.slf4j.LoggerFactory

object JobExecutor {

  val log = LoggerFactory.getLogger("com.ing.baker.petrinet.runtime.JobExecutor")

  /**
   * Returns a Job -> IO[TransitionEvent]
   */
  def apply[S, P[_], T[_], E](taskProvider: TransitionTaskProvider[P, T, S, E],
            exceptionHandlerFn: ExceptionHandler[P, T, S])
           (topology: PetriNet[P[_], T[_]]): Job[P, T, S] ⇒ IO[TransitionEvent[T]] = {

    val cachedTransitionTasks: Map[T[_], _] =
      topology.transitions.map(t ⇒ t -> taskProvider.apply[Any](topology, t.asInstanceOf[T[Any]])).toMap

    def transitionFunction[Input](t: T[Input]) =
      cachedTransitionTasks(t).asInstanceOf[TransitionTask[P, Input, S, E]]

    def exceptionStackTrace(e: Throwable): String = {
      val sw = new StringWriter()
      e.printStackTrace(new PrintWriter(sw))
      sw.toString
    }

    job ⇒ {

      val startTime = System.currentTimeMillis()
      val transition = job.transition.asInstanceOf[T[Any]]

      val jobIO =
        try {
          // calling the transition function could potentially throw an exception
          transitionFunction(transition)(job.consume, job.processState, job.input)
        } catch {
          case e: Throwable ⇒ IO.raiseError(e)
        }

      // translates the job output to an EventSourcing.Event
      jobIO.map {
        case (produced, out) ⇒
          TransitionFiredEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, produced, out)
      }.handle {
        // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
        case e: Throwable ⇒
          val failureCount = job.failureCount + 1
          val failureStrategy = exceptionHandlerFn.handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
          TransitionFailedEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, job.input, exceptionStackTrace(e), failureStrategy)
      }.handle {
        // If an exception was thrown while computing the failure strategy we block the interaction from firing
        case e: Throwable =>
          log.error(s"Exception while handling transition failure", e)
          TransitionFailedEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, job.input, exceptionStackTrace(e), ExceptionStrategy.BlockTransition)
      }
    }
  }
}
