package com.ing.baker.petrinet.dsl.colored

import com.ing.baker.petrinet.api._
import fs2.Task
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import com.ing.baker.petrinet.runtime._

import scala.util.Random

trait StateTransitionNet[S, E] {

  def eventSourceFunction: S ⇒ E ⇒ S

  def eventTaskProvider: TransitionTaskProvider[S, Place, Transition] = new TransitionTaskProvider[S, Place, Transition] {
    override def apply[Input, Output](petriNet: PetriNet[Place[_], Transition[_, _]], t: Transition[Input, Output]): TransitionTask[Place, Input, Output, S] =
      (_, state, _) ⇒ {
        val eventTask = t.asInstanceOf[StateTransition[S, Output]].produceEvent(state)
        val produceMarking: Marking[Place] = toMarking[Place](petriNet.outMarking(t))
        eventTask.map(e ⇒ (produceMarking, e))
      }
  }

  val runtime: PetriNetRuntime[Place, Transition, S, E] = new PetriNetRuntime[Place, Transition, S, E] {
    override val eventSourceFn: (Transition[_, _]) ⇒ (S) ⇒ (E) ⇒ S = _ ⇒ eventSourceFunction
    override val taskProvider: TransitionTaskProvider[S, Place, Transition] = eventTaskProvider
    override val exceptionHandlerFn: (Transition[_, _]) => TransitionExceptionHandler[Place] = (t: Transition[_, _]) ⇒ t.exceptionStrategy
    override lazy val jobPicker = new JobPicker[Place, Transition](tokenGame) {
      override def isAutoFireable[T](instance: Instance[Place, Transition, T], t: Transition[_, _]): Boolean =
        t.isAutomated && instance.isBlockedReason(t).isEmpty
    }
  }

  def stateTransition(id: Long = Math.abs(Random.nextLong), label: Option[String] = None, automated: Boolean = false,
    exceptionStrategy: TransitionExceptionHandler[Place] = (_, _, _) ⇒ BlockTransition)(fn: S ⇒ E): Transition[Unit, E] =
    StateTransition(id, label.getOrElse(s"t$id"), automated, exceptionStrategy, (s: S) ⇒ Task.now(fn(s)))

  def constantTransition[I, O](id: Long, label: Option[String] = None, automated: Boolean = false, constant: O): StateTransition[I, O] =
    StateTransition[I, O](id, label.getOrElse(s"t$id"), automated, (_, _, _) ⇒ BlockTransition, _ ⇒ Task.now(constant))

  def nullTransition[O](id: Long, label: Option[String] = None, automated: Boolean = false): Transition[Unit, O] =
    constantTransition[Unit, O](id, label, automated, ().asInstanceOf[O])
}
