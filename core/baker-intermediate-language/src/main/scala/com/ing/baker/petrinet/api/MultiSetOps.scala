package com.ing.baker.petrinet.api

trait MultiSetOps {

  implicit class MultiSetFunctions[X](mset: MultiSet[X]) {
    def multisetDifference(other: MultiSet[X]): MultiSet[X] =
      other.foldLeft(mset) {
        case (result, (p, count)) => result.get(p) match {
          case None                  => result
          case Some(n) if n <= count => result - p
          case Some(n)               => result + (p -> (n - count))
        }
      }

    def multisetSum(other: MultiSet[X]): MultiSet[X] =
      other.foldLeft(mset) {
        case (m, (p, count)) => m.get(p) match {
          case None    => m + (p -> count)
          case Some(n) => m + (p -> (n + count))
        }
      }

    /**
      * This checks that the given (other) multiset is a sub set of this one.
      *
      * @param other
      * @return
      */
    def isSubSet(other: MultiSet[X]): Boolean =
      !other.exists {
        case (element, count) => mset.get(element) match {
          case None                 => true
          case Some(n) if n < count => true
          case _                    => false
        }
      }

    def multisetSize: Int = mset.values.sum

    def setMultiplicity(map: Map[X, Int])(element: X, m: Int) = map + (element -> m)

    def allElements: Iterable[X] = mset.foldLeft(List.empty[X]) {
      case (list, (e, count)) => List.fill[X](count)(e) ::: list
    }

    def multisetDecrement(element: X, count: Int): MultiSet[X] =
      mset.get(element) match {
        case None                  => mset
        case Some(n) if n <= count => mset - element
        case Some(n)               => mset + (element -> (n - count))
      }

    def multisetIncrement(element: X, count: Int): MultiSet[X] = mset + (element -> (count + mset.getOrElse(element, 0)))

    def multisetIntersects(other: MultiSet[X]): Boolean = {
      mset.exists { case (p, n) => other.getOrElse(p, 0) > 0 }
    }
  }
}
