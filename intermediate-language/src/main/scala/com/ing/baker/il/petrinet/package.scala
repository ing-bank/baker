package com.ing.baker.il

import com.ing.baker.petrinet.api._
import scalax.collection.edge.WLDiEdge

package object petrinet {

  type RecipePetriNet = PetriNet[Place[_], Transition]

  def arc(t: Transition, p: Place[_], weight: Long): Arc = WLDiEdge[Node, Edge[Any]](Right(t), Left(p))(weight, Edge[Any](None))

  def arc[C](p: Place[C], t: Transition, weight: Long, eventFilter: Option[String] = None): Arc = {
    WLDiEdge[Node, Edge[C]](Left(p), Right(t))(weight, Edge[C](eventFilter))
  }

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place[_], Transition]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.id)

  implicit def transitionIdentifier(t: Transition): Id = Id(t.id)
}
