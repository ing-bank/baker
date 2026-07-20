package com.ing.baker.runtime.akka.actor.process_instance.dsl

import cats.effect.IO
import com.ing.baker.il.petrinet.Place
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.dsl.TestUtils.PlaceMethods
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.BlockTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}


case class TransitionBehaviour(
    automated: Boolean,
    exceptionHandler: TransitionExceptionHandler[Place],
    fn: RecipeInstanceState => EventInstance) {

  def asTransition(id: Long) = StateTransition(id, s"t$id", automated, exceptionHandler, state => IO { (fn(state)) })
}

/**
  * Wrapper for a simple sequence petri net:
  *
  * p1 -> t1 -> p2 -> t2 -> ... -> tn -> pn+1
  *
  * The net starts with a place and ends with a place.
  */
trait SequenceNet extends StateTransitionNet {

  def sequence: Seq[TransitionBehaviour]

  lazy val places: Seq[Place] = (1 to (sequence.size + 1)).map(i => TestUtils.place(i))
  lazy val initialMarking: Marking[Place] = place(1).markWithN(1)

  def place(n: Int) = places(n - 1)

  def transition(automated: Boolean = false, exceptionHandler: TransitionExceptionHandler[Place] = (e, n, _) => BlockTransition)(fn: RecipeInstanceState => EventInstance): TransitionBehaviour = TransitionBehaviour(automated, exceptionHandler, fn)

  lazy val petriNet = {
    val nrOfSteps = sequence.size
    val transitions = sequence.zipWithIndex.map { case (t, index) => t.asTransition(index + 1) }

    val places = (1 to (nrOfSteps + 1)).map(i => TestUtils.place(id = i))
    val tpedges = transitions.zip(places.tail).map { case (t, p) => arc(t, p, 1) }
    val ptedges = places.zip(transitions).map { case (p, t) => arc(p, t, 1) }
    createPetriNet[RecipeInstanceState]((tpedges ++ ptedges): _*)
  }
}