package com.ing.baker.petrinet.api

object Marking {

  /**
    * Returns the empty marking.
    *
    * @return The empty marking.
    */
  def empty[X]: Marking[X] = Map.empty[X, MultiSet[Any]]
}