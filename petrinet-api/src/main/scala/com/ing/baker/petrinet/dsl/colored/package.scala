package com.ing.baker.petrinet.dsl

import com.ing.baker.petrinet.api._

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object colored {

  /**
   * Type alias for the node type of the scalax.collection.Graph backing the petri net.
   */
  type Node = Either[Place[_], Transition[_]]

  /**
   * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
   */
  type Arc = WLDiEdge[Node]

  /**
   * Type alias for a colored petri net.
   */
  type ColoredPetriNet = PetriNet[Place[_], Transition[_]]

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.id)

  implicit def transitionIdentifier(t: Transition[_]): Id = Id(t.id)

  implicit class TransitionDSL[Input, Output, State](t: Transition[Input]) {
    def ~>(p: Place[_], weight: Long = 1): Arc = arc(t, p, weight)
  }

  implicit class PlaceDSL[C](p: Place[C]) {
    def ~>(t: Transition[_], weight: Long = 1): Arc = arc(p, t, weight)
  }

  def arc(t: Transition[_], p: Place[_], weight: Long): Arc = WLDiEdge[Node, String](Right(t), Left(p))(weight, "")

  def arc[C](p: Place[C], t: Transition[_], weight: Long): Arc = WLDiEdge[Node, String](Left(p), Right(t))(weight, "")

  def createPetriNet[S](params: Arc*): ColoredPetriNet = {
    val petriNet = new ScalaGraphPetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }
}
