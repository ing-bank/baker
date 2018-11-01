package com.ing.baker.petrinet.dsl

import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.ExceptionStrategy

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object colored {

  /**
   * Type alias for the node type of the scalax.collection.Graph backing the petri net.
   */
  type Node = Either[Place[_], Transition]

  /**
    * An exception handler function associated with a transition.
    */
  type TransitionExceptionHandler[P[_]] = (Throwable, Int, MultiSet[P[_]]) ⇒ ExceptionStrategy

  /**
   * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
   */
  type Arc = WLDiEdge[Node]

  /**
   * Type alias for a colored petri net.
   */
  type ColoredPetriNet = PetriNet[Place[_], Transition]

  implicit class TransitionDSL[Input, Output, State](t: Transition) {
    def ~>(p: Place[_], weight: Long = 1): Arc = arc(t, p, weight)
  }

  implicit class PlaceDSL[C](p: Place[C]) {
    def ~>(t: Transition, weight: Long = 1): Arc = arc(p, t, weight)
  }

  def arc(t: Transition, p: Place[_], weight: Long): Arc = WLDiEdge[Node, String](Right(t), Left(p))(weight, "")

  def arc[C](p: Place[C], t: Transition, weight: Long): Arc = WLDiEdge[Node, String](Left(p), Right(t))(weight, "")

  def requireUniqueElements[T](i: Iterable[T], name: String = "Element"): Unit = {
    (Set.empty[T] /: i) { (set, e) ⇒
      if (set.contains(e))
        throw new IllegalArgumentException(s"$name '$e' is not unique!")
      else
        set + e
    }
  }

  def createPetriNet[S](params: Arc*): ColoredPetriNet = {
    val petriNet = new PetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }
}
