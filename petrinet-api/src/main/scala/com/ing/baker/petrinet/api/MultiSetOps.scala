package com.ing.baker.petrinet.api

trait MultiSetOps {

  implicit class MultiSetFunctions[T](mset: MultiSet[T]) {
    def multisetDifference(other: MultiSet[T]): MultiSet[T] =
      other.foldLeft(mset) {
        case (result, (p, count)) ⇒ result.get(p) match {
          case None                  ⇒ result
          case Some(n) if n <= count ⇒ result - p
          case Some(n)               ⇒ result + (p -> (n - count))
        }
      }

    def multisetSum(other: MultiSet[T]): MultiSet[T] =
      other.foldLeft(mset) {
        case (m, (p, count)) ⇒ m.get(p) match {
          case None    ⇒ m + (p -> count)
          case Some(n) ⇒ m + (p -> (n + count))
        }
      }

    def isSubSet(other: MultiSet[T]): Boolean =
      !other.exists {
        case (element, count) ⇒ mset.get(element) match {
          case None                 ⇒ true
          case Some(n) if n < count ⇒ true
          case _                    ⇒ false
        }
      }

    def multisetSize: Int = mset.values.sum

    def multiplicities(map: MultiSet[T]): Map[T, Int] = map

    def setMultiplicity(map: Map[T, Int])(element: T, m: Int) = map + (element -> m)

    def allElements: Iterable[T] = mset.foldLeft(List.empty[T]) {
      case (list, (e, count)) ⇒ List.fill[T](count)(e) ::: list
    }

    def multisetDecrement(element: T, count: Int): MultiSet[T] =
      mset.get(element) match {
        case None                  ⇒ mset
        case Some(n) if n <= count ⇒ mset - element
        case Some(n)               ⇒ mset + (element -> (n - count))
      }

    def multisetIncrement(element: T, count: Int): MultiSet[T] = mset + (element -> (count + mset.getOrElse(element, 0)))

    def multisetIntersects(other: MultiSet[T]): Boolean = {
      mset.exists { case (p, n) ⇒ other.getOrElse(p, 0) > 0 }
    }
  }
}
