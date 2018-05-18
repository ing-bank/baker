package com.ing.baker.petrinet.dsl.colored

import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime._

import scala.util.Random

trait StateTransitionNet[S, E] {

  def eventSourceFunction: S ⇒ E ⇒ S

  def eventTaskProvider: TransitionTaskProvider[Place, Transition, S, E] = new TransitionTaskProvider[Place, Transition, S, E] {
    override def apply[Input](petriNet: PetriNet[Place[_], Transition[_]], t: Transition[Input]): TransitionTask[Place, Input, S, E] =
      (_, state, _) ⇒ {
        val eventTask = t.asInstanceOf[StateTransition[S, E]].produceEvent(state)
        val produceMarking: Marking[Place] = toMarking[Place](petriNet.outMarking(t))
        eventTask.map(e ⇒ (produceMarking, e))
      }
  }

  val runtime: PetriNetRuntime[Place, Transition, S, E] = new PetriNetRuntime[Place, Transition, S, E] {
    override val eventSource: (Transition[_]) ⇒ (S) ⇒ (E) ⇒ S = _ ⇒ eventSourceFunction
    override val taskProvider: TransitionTaskProvider[Place, Transition, S, E] = eventTaskProvider
    override val exceptionHandler: ExceptionHandler[Place, Transition, S] = new ExceptionHandler[Place, Transition, S] {
      override def handleException(job: Job[Place, Transition, S])
                                  (throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place[_]]) =
        job.transition.exceptionStrategy(throwable, failureCount, outMarking)
    }
    override lazy val jobPicker = new JobPicker[Place, Transition](tokenGame) {
      override def isAutoFireable[S](instance: Instance[Place, Transition, S], t: Transition[_]): Boolean =
        t.isAutomated && instance.isBlockedReason(t).isEmpty
    }
  }

  def stateTransition(id: Long = Math.abs(Random.nextLong), label: Option[String] = None, automated: Boolean = false,
    exceptionStrategy: TransitionExceptionHandler[Place] = (_, _, _) ⇒ BlockTransition)(fn: S ⇒ E): Transition[Unit] =
    StateTransition(id, label.getOrElse(s"t$id"), automated, exceptionStrategy, (s: S) ⇒ IO.pure(fn(s)))

  def constantTransition[I, O](id: Long, label: Option[String] = None, automated: Boolean = false, constant: O): StateTransition[I, O] =
    StateTransition[I, O](id, label.getOrElse(s"t$id"), automated, (_, _, _) ⇒ BlockTransition, _ ⇒ IO.pure(constant))

  def nullTransition[O](id: Long, label: Option[String] = None, automated: Boolean = false): Transition[Unit] =
    constantTransition[Unit, O](id, label, automated, ().asInstanceOf[O])
}
