package io.kagera.dsl.colored

import fs2.Task
import io.kagera.api._
import io.kagera.runtime.ExceptionStrategy.BlockTransition
import io.kagera.runtime.TransitionExceptionHandler

case class TransitionBehaviour[S, E](automated: Boolean, exceptionHandler: TransitionExceptionHandler, fn: S ⇒ E) {
  def asTransition(id: Long) = StateTransition[S, E](id, s"t$id", automated, exceptionHandler, state ⇒ Task.delay { (fn(state)) })
}

trait SequenceNet[S, E] extends StateTransitionNet[S, E] {

  def sequence: Seq[TransitionBehaviour[S, E]]

  lazy val places = (1 to (sequence.size + 1)).map(i ⇒ Place[Unit](id = i, label = s"p$i"))
  lazy val initialMarking = Marking(place(1) -> 1)

  def place(n: Int) = places(n - 1)

  def transition(automated: Boolean = false, exceptionHandler: TransitionExceptionHandler = (e, n) ⇒ BlockTransition)(fn: S ⇒ E): TransitionBehaviour[S, E] = TransitionBehaviour(automated, exceptionHandler, fn)

  lazy val petriNet = {
    val nrOfSteps = sequence.size
    val transitions = sequence.zipWithIndex.map { case (t, index) ⇒ t.asTransition(index + 1) }

    val places = (1 to (nrOfSteps + 1)).map(i ⇒ Place[Unit](id = i, label = s"p$i"))
    val tpedges = transitions.zip(places.tail).map { case (t, p) ⇒ arc(t, p, 1) }
    val ptedges = places.zip(transitions).map { case (p, t) ⇒ arc(p, t, 1) }
    createPetriNet[S]((tpedges ++ ptedges): _*)
  }
}