package com.ing.baker.petrinet.api

object Marking {

  /**
    * Returns the empty marking.
    *
    * @return The empty marking.
    */
  def empty[P]: Marking[P] = Map.empty[P, MultiSet[Any]]

  def apply[P](m1: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1)
  }

  def apply[P](m1: MarkedPlace[P], m2: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2)
  }

  def apply[P](m1: MarkedPlace[P], m2: MarkedPlace[P], m3: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2, m3)
  }

  def apply[P](m1: MarkedPlace[P], m2: MarkedPlace[P], m3: MarkedPlace[P], m4: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2, m3, m4)
  }

  def apply[P](m1: MarkedPlace[P], m2: MarkedPlace[P], m3: MarkedPlace[P], m4: MarkedPlace[P], m5: MarkedPlace[P]): Marking[P] = {
    Map[P, MultiSet[Any]](m1, m2, m3, m4, m5)
  }
}