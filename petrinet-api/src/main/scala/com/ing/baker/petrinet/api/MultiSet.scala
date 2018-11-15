package com.ing.baker.petrinet.api

object MultiSet {

  /**
   * The empty multi set.
   */
  def empty[T]: MultiSet[T] = Map.empty[T, Int]

  /**
   * Copies a the given elements into a multi set.
   *
   * Equal elements in the sequence will increase the multiplicity of that element in multi set.
   */
  def copyOff[T](elements: Iterable[T]): MultiSet[T] = elements.foldLeft(empty[T]) { case (mset, e) ⇒ mset.multisetIncrement(e, 1) }

  /**
    * Creates a multiset of the provided elements.
    *
    * Equal elements in the arguments will increase the multiplicity of that element in multi set.
    */
  def apply[T](elements: T*): MultiSet[T] = copyOff[T](elements)
}
