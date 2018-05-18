package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api.{MultiSet, PetriNet}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition

/**
 * Encapsulates all components required to 'run' a petri net instance
 *
 * @tparam P The place type
 * @tparam T The transition type
 * @tparam S The state type
 * @tparam E The event type
 */
trait PetriNetRuntime[P[_], T[_], S, E] {

  val tokenGame: TokenGame[P, T] = new TokenGame[P, T] {}

  val eventSource: T[_] ⇒ (S ⇒ E ⇒ S) = _ ⇒ (s ⇒ _ ⇒ s)

  val exceptionHandler: ExceptionHandler[P, T, S] = new ExceptionHandler[P, T, S] {
    override def handleException(job: Job[P, T, S])(throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[P[_]]) = BlockTransition
  }

  val taskProvider: TransitionTaskProvider[P, T, S, E]

  def jobExecutor(topology: PetriNet[P[_], T[_]]) = JobExecutor[S, P, T, E](taskProvider, exceptionHandler)(topology)

  lazy val jobPicker = new JobPicker[P, T](tokenGame)
}