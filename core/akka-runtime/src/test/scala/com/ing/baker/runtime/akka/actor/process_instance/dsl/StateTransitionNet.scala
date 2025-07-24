package com.ing.baker.runtime.akka.actor.process_instance.dsl

import cats.effect.IO
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.dsl.TestUtils
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceRuntime
import com.ing.baker.runtime.akka.actor.process_instance.dsl.TestUtils.TransitionMethods
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.BlockTransition
import com.ing.baker.runtime.akka.actor.process_instance.internal._
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}

import scala.util.Random

trait StateTransitionNet {

  def eventSourceFunction: RecipeInstanceState => EventInstance => RecipeInstanceState

  val runtime: ProcessInstanceRuntime = new ProcessInstanceRuntime {
    override val eventSource: (Long, com.ing.baker.il.petrinet.Transition) => RecipeInstanceState => EventInstance => RecipeInstanceState = (_, _) => eventSourceFunction

    override def transitionTask(petriNet: PetriNet, t: com.ing.baker.il.petrinet.Transition)
                               (marking: Marking[Place], state: RecipeInstanceState, input: Any): IO[(Marking[Place], EventInstance)] = {
      val eventTask = t.asInstanceOf[StateTransition].produceEvent(state)
      val produceMarking: Marking[Place] = petriNet.outMarking(t).toMarking
      eventTask.map(e => (produceMarking, e))
    }

    override def handleException(job: Job[RecipeInstanceState])
                                (throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place]): ExceptionStrategy =
      job.transition.exceptionStrategy(throwable, failureCount, outMarking)

    override def canBeFiredAutomatically(instance: Instance[RecipeInstanceState], t: com.ing.baker.il.petrinet.Transition): Boolean =
      t.isAutomated && !instance.isBlocked(t)
  }

  def stateTransition(id: Long = Math.abs(Random.nextLong()), label: Option[String] = None, automated: Boolean = false,
                      exceptionStrategy: TransitionExceptionHandler[Place] = (_, _, _) => BlockTransition)(fn: RecipeInstanceState => EventInstance): Transition =
    StateTransition(id, label.getOrElse(s"t$id"), automated, exceptionStrategy, (s: RecipeInstanceState) => IO.pure(fn(s)))

  def constantTransition(id: Long, label: Option[String] = None, automated: Boolean = false, constant: EventInstance): StateTransition =
    StateTransition(id, label.getOrElse(s"t$id"), automated, (_, _, _) => BlockTransition, _ => IO.pure(constant))

  def emptyTransition(id: Long, label: Option[String] = None, automated: Boolean = false): Transition =
    constantTransition(id, label, automated, EventInstance("name"))
}
