package com.ing.baker.petrinet.runtime

import java.io.{PrintWriter, StringWriter}

import cats.effect.IO
import com.ing.baker.petrinet.api.{MultiSet, PetriNet}
import com.ing.baker.petrinet.runtime.EventSourcing.{TransitionEvent, TransitionFailedEvent, TransitionFiredEvent}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import org.slf4j.LoggerFactory

/**
 * Encapsulates all components required to 'run' a petri net instance
 *
 * @tparam P The place type
 * @tparam T The transition type
 * @tparam S The state type
 * @tparam E The event type
 */
trait PetriNetRuntime[P, T, S, E] {

  val log = LoggerFactory.getLogger("com.ing.baker.petrinet.runtime.PetriNetRuntime")

  val tokenGame: TokenGame[P, T] = new TokenGame[P, T] {}

  val eventSource: T ⇒ (S ⇒ E ⇒ S) = _ ⇒ (s ⇒ _ ⇒ s)

  val exceptionHandler: ExceptionHandler[P, T, S] = new ExceptionHandler[P, T, S] {
    override def handleException(job: Job[P, T, S])(throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[P]) = BlockTransition
  }

  val taskProvider: TransitionTaskProvider[P, T, S, E]

  /**
    * Returns a Job -> IO[TransitionEvent]
    */
  def jobExecutor(topology: PetriNet[P, T]): Job[P, T, S] ⇒ IO[TransitionEvent[T]] = {

    val cachedTransitionTasks: Map[T, _] =
      topology.transitions.map(t ⇒ t -> taskProvider.apply(topology, t)).toMap

    def transitionFunction(t: T) =
      cachedTransitionTasks(t).asInstanceOf[TransitionTask[P, S, E]]

    def exceptionStackTrace(e: Throwable): String = {
      val sw = new StringWriter()
      e.printStackTrace(new PrintWriter(sw))
      sw.toString
    }

    job ⇒ {

      val startTime = System.currentTimeMillis()
      val transition = job.transition

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
          val failureStrategy = exceptionHandler.handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
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