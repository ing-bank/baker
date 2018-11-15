package com.ing.baker.il

import com.ing.baker.petrinet.api._
import scalax.collection.edge.WLDiEdge

package object petrinet {

  /**
    * Type alias for a petri net with recipe Place and Transition types
    */
  type RecipePetriNet = PetriNet[Place, Transition]

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place, Transition]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]
}
