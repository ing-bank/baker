package com.ing.baker.petrinet.runtime

import java.io.{PrintWriter, StringWriter}

import com.ing.baker.petrinet.api._
import fs2.{Strategy, Task}
import com.ing.baker.petrinet.runtime.EventSourcing._

/**
 * Class responsible for 'executing' a transition 'Job'
 */
class JobExecutor[S, P[_], T[_, _]](
    taskProvider: TransitionTaskProvider[S, P, T],
    exceptionHandlerFn: T[_, _] ⇒ TransitionExceptionHandler) {

  /**
   * Executes a job returning a Task[TransitionEvent]
   */
  def apply(topology: PetriNet[P[_], T[_, _]])(implicit strategy: Strategy): Job[P, T, S, _] ⇒ Task[TransitionEvent[T]] = {

    val cachedTransitionTasks: Map[T[_, _], _] =
      topology.transitions.map(t ⇒ t -> taskProvider.apply[Any, Any](topology, t.asInstanceOf[T[Any, Any]])).toMap

    def transitionFunction[Input, Output](t: T[Input, Output]) =
      cachedTransitionTasks(t).asInstanceOf[TransitionTask[P, Input, Output, S]]

    def executeTransitionAsync[Input, Output](t: T[Input, Output]): TransitionTask[P, Input, Output, S] = {
      (consume, state, input) ⇒

        val handleFailure: PartialFunction[Throwable, Task[(Marking[P], Output)]] = {
          case e: Throwable ⇒ Task.fail(e)
        }

        try {
          transitionFunction(t)(consume, state, input).handleWith { handleFailure }.async
        } catch { handleFailure }
    }

    job ⇒ {

      val startTime = System.currentTimeMillis()
      val transition = job.transition.asInstanceOf[T[Any, Any]]

      executeTransitionAsync(transition)(job.consume, job.processState, job.input).map {
        case (produced, out) ⇒
          TransitionFiredEvent(job.id, transition, startTime, System.currentTimeMillis(), job.consume, produced, out)
      }.handle {
        case e: Throwable ⇒
          val failureCount = job.failureCount + 1
          val failureStrategy = exceptionHandlerFn(transition).apply(e, failureCount)

          val sw = new StringWriter()
          e.printStackTrace(new PrintWriter(sw))
          val stackTraceString = sw.toString

          TransitionFailedEvent(job.id, transition, startTime, System.currentTimeMillis(), job.consume, job.input, stackTraceString, failureStrategy)
      }
    }
  }
}
