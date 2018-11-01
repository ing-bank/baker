package com.ing.baker.petrinet.api

object Marking {

  /**
    * Returns the empty marking.
    *
    * @return The empty marking.
    */
  def empty[P]: Marking[P] = Map.empty[P, MultiSet[Any]]
}