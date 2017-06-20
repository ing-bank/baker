package com.ing.baker.il

import io.kagera.api._

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object petrinet {

  type RecipePetriNet = PetriNet[Place[_], Transition[_, _]]

  def arc(t: Transition[_, _], p: Place[_], weight: Long): Arc = WLDiEdge[Node, String](Right(t), Left(p))(weight, "")

  def arc[C](p: Place[C], t: Transition[_, _], weight: Long, filter: C ⇒ Boolean = (token: C) ⇒ true): Arc = {
    val innerEdge = new PTEdge[C](weight, filter)
    WLDiEdge[Node, PTEdge[C]](Left(p), Right(t))(weight, innerEdge)
  }

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place[_], Transition[_, _]]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  implicit def placeLabel[C](p: Place[C]): Label = Label(p.label)

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.id)

  implicit def transitionLabeler(t: Transition[_, _]): Label = Label(t.label)

  implicit def transitionIdentifier(t: Transition[_, _]): Id = Id(t.id)

  def createPetriNet(params: Arc*): RecipePetriNet = {
    val petriNet = new ScalaGraphPetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }

}
