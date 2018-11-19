package com.ing.baker.runtime.actor.process_instance.dsl

import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceRuntime
import com.ing.baker.runtime.actor.process_instance.internal.ExceptionStrategy.BlockTransition
import com.ing.baker.runtime.actor.process_instance.internal._

import scala.util.Random

trait StateTransitionNet[S, E] {

  def eventSourceFunction: S ⇒ E ⇒ S

  val runtime: ProcessInstanceRuntime[Place, Transition, S, E] = new ProcessInstanceRuntime[Place, Transition, S, E] {
    override val eventSource: (Transition) ⇒ (S) ⇒ (E) ⇒ S = _ ⇒ eventSourceFunction
    override def transitionTask(petriNet: PetriNet[Place, Transition], t: Transition)
                               (marking: Marking[Place], state: S, input: Any): IO[(Marking[Place], E)] = {
      val eventTask = t.asInstanceOf[StateTransition[S, E]].produceEvent(state)
      val produceMarking: Marking[Place] = petriNet.outMarking(t).toMarking
      eventTask.map(e ⇒ (produceMarking, e))
    }
    override def handleException(job: Job[Place, Transition, S])
                                (throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place]) =
      job.transition.exceptionStrategy(throwable, failureCount, outMarking)
    override def isAutoFireable(instance: Instance[Place, Transition, S], t: Transition): Boolean =
      t.isAutomated && instance.isBlockedReason(t).isEmpty
  }

  def stateTransition(id: Long = Math.abs(Random.nextLong), label: Option[String] = None, automated: Boolean = false,
    exceptionStrategy: TransitionExceptionHandler[Place] = (_, _, _) ⇒ BlockTransition)(fn: S ⇒ E): Transition =
    StateTransition(id, label.getOrElse(s"t$id"), automated, exceptionStrategy, (s: S) ⇒ IO.pure(fn(s)))

  def constantTransition[I, O](id: Long, label: Option[String] = None, automated: Boolean = false, constant: O): StateTransition[I, O] =
    StateTransition[I, O](id, label.getOrElse(s"t$id"), automated, (_, _, _) ⇒ BlockTransition, _ ⇒ IO.pure(constant))

  def nullTransition[O](id: Long, label: Option[String] = None, automated: Boolean = false): Transition =
    constantTransition[Unit, O](id, label, automated, ().asInstanceOf[O])
}
