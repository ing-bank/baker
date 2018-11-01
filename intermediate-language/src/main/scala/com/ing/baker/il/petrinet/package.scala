package com.ing.baker.il

import com.ing.baker.petrinet.api._
import scalax.collection.edge.WLDiEdge

package object petrinet {

  type RecipePetriNet = PetriNet[Place, Transition]

  def arc(t: Transition, p: Place, weight: Long): Arc = WLDiEdge[Node, Edge](Right(t), Left(p))(weight, Edge(None))

  def arc(p: Place, t: Transition, weight: Long, eventFilter: Option[String] = None): Arc = {
    WLDiEdge[Node, Edge](Left(p), Right(t))(weight, Edge(eventFilter))
  }

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place, Transition]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]
}
