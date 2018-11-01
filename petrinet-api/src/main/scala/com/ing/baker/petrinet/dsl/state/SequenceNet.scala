package com.ing.baker.petrinet.dsl.state

import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.dsl.colored.{Place, TransitionExceptionHandler, arc, createPetriNet}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition


case class TransitionBehaviour[S, E](
    automated: Boolean,
    exceptionHandler: TransitionExceptionHandler[Place],
    fn: S ⇒ E) {

  def asTransition(id: Long) = StateTransition[S, E](id, s"t$id", automated, exceptionHandler, state ⇒ IO { (fn(state)) })
}

trait SequenceNet[S, E] extends StateTransitionNet[S, E] {

  def sequence: Seq[TransitionBehaviour[S, E]]

  lazy val places: Seq[Place] = (1 to (sequence.size + 1)).map(i ⇒ Place(id = i, label = s"p$i"))
  lazy val initialMarking: Marking[Place] = place(1).markWithN(1)

  def place(n: Int) = places(n - 1)

  def transition(automated: Boolean = false, exceptionHandler: TransitionExceptionHandler[Place] = (e, n, _) ⇒ BlockTransition)(fn: S ⇒ E): TransitionBehaviour[S, E] = TransitionBehaviour(automated, exceptionHandler, fn)

  lazy val petriNet = {
    val nrOfSteps = sequence.size
    val transitions = sequence.zipWithIndex.map { case (t, index) ⇒ t.asTransition(index + 1) }

    val places = (1 to (nrOfSteps + 1)).map(i ⇒ Place(id = i, label = s"p$i"))
    val tpedges = transitions.zip(places.tail).map { case (t, p) ⇒ arc(t, p, 1) }
    val ptedges = places.zip(transitions).map { case (p, t) ⇒ arc(p, t, 1) }
    createPetriNet[S]((tpedges ++ ptedges): _*)
  }
}