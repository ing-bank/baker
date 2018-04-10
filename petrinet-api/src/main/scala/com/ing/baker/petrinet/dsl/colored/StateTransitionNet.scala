package com.ing.baker.petrinet.dsl.colored

import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime._

import scala.util.Random

trait StateTransitionNet[S, E] {

  def eventSourceFunction: S ⇒ E ⇒ S

  def eventTaskProvider: TransitionTaskProvider[S, Place, Transition] = new TransitionTaskProvider[S, Place, Transition] {
    override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_]], t: Transition[Input]): TransitionTask[Place, Input, Output, S] =
      (_, state, _) ⇒ {
        val eventTask = t.asInstanceOf[StateTransition[S, Output]].produceEvent(state)
        val produceMarking: Marking[Place] = toMarking[Place](petriNet.outMarking(t))
        eventTask.map(e ⇒ (produceMarking, e))
      }
  }

  val runtime: PetriNetRuntime[Place, Transition, S, E] = new PetriNetRuntime[Place, Transition, S, E] {
    override val eventSourceFn: (Transition[_]) ⇒ (S) ⇒ (E) ⇒ S = _ ⇒ eventSourceFunction
    override val taskProvider: TransitionTaskProvider[S, Place, Transition] = eventTaskProvider
    override val exceptionHandlerFn: (Transition[_]) => TransitionExceptionHandler[Place] = (t: Transition[_]) ⇒ t.exceptionStrategy
    override lazy val jobPicker = new JobPicker[Place, Transition](tokenGame) {
      override def isAutoFireable[S, E](instance: Instance[Place, Transition, S, E], t: Transition[_]): Boolean =
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
