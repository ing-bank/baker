package com.ing.baker.runtime.actor.process_instance

import com.ing.baker.petrinet.api.{MultiSet, PetriNet}
import com.ing.baker.runtime.actor.process_instance.internal.ExceptionStrategy
import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object dsl {

  /**
    * An exception handler function associated with a transition.
    */
  type TransitionExceptionHandler[P] = (Throwable, Int, MultiSet[P]) ⇒ ExceptionStrategy

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place, Transition]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  implicit class TransitionDSL(t: Transition) {
    def ~>(p: Place, weight: Long = 1): Arc = arc(t, p, weight)
  }

  implicit class PlaceDSL(p: Place) {
    def ~>(t: Transition, weight: Long = 1): Arc = arc(p, t, weight)
  }

  def arc(t: Transition, p: Place, weight: Long): Arc = WLDiEdge[Node, String](Right(t), Left(p))(weight, "")

  def arc(p: Place, t: Transition, weight: Long): Arc = WLDiEdge[Node, String](Left(p), Right(t))(weight, "")

  def requireUniqueElements[T](i: Iterable[T], name: String = "Element"): Unit = {
    (Set.empty[T] /: i) { (set, e) ⇒
      if (set.contains(e))
        throw new IllegalArgumentException(s"$name '$e' is not unique!")
      else
        set + e
    }
  }

  def createPetriNet[S](params: Arc*): PetriNet[Place, Transition] = {
    val petriNet = new PetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }
}
