package com.ing.baker.petrinet.api

object MultiSet {

  /**
   * The empty multi set.
   */
  def empty[X]: MultiSet[X] = Map.empty[X, Int]

  /**
   * Copies a the given elements into a multi set.
   *
   * Equal elements in the sequence will increase the multiplicity of that element in multi set.
   */
  def copyOff[X](elements: Iterable[X]): MultiSet[X] = elements.foldLeft(empty[X]) { case (mset, e) => mset.multisetIncrement(e, 1) }

  /**
    * Creates a multiset of the provided elements.
    *
    * Equal elements in the arguments will increase the multiplicity of that element in multi set.
    */
  def apply[X](elements: X*): MultiSet[X] = copyOff[X](elements)
}
