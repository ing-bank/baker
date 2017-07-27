package io.kagera.api

trait MarkingOps {

  /**
   * Some convenience method additions to work with Markings.
   */
  implicit class MarkingFunctions[P[_]](marking: Marking[P]) {

    // Note: extra .map(identity) is a needed to workaround the scala Map serialization bug: https://issues.scala-lang.org/browse/SI-7005
    def multiplicities: MultiSet[P[_]] = marking.data.mapValues(_.multisetSize).map(identity)

    def add[C](p: P[C], value: C, count: Int = 1): Marking[P] = {
      val newTokens = marking.getOrElse(p, MultiSet.empty).multisetIncrement(value, count)
      marking.+(p -> newTokens)
    }

    def |-|(other: Marking[P]): Marking[P] = other.keySet.foldLeft(marking) {

      case (result, place) ⇒
        val p = place.asInstanceOf[P[Any]]
        marking.get(p) match {
          case None ⇒ result
          case Some(tokens) ⇒
            val newTokens = tokens.multisetDifference(other(p))
            if (newTokens.isEmpty)
              result - p
            else
              result + (p -> newTokens)
        }
    }

    def |+|(other: Marking[P]): Marking[P] = other.keySet.foldLeft(marking) {
      case (result, place) ⇒
        val p = place.asInstanceOf[P[Any]]
        val newTokens = marking.get(p) match {
          case None         ⇒ other(p)
          case Some(tokens) ⇒ tokens.multisetSum(other(p))
        }

        result + (p -> newTokens)
    }
  }

  implicit def toMarkedPlace[P[_]](tuple: (P[Unit], Int)): MarkedPlace[P, Unit] = tuple._1 -> Map[Unit, Int](() -> tuple._2)

  implicit class IterableToMarking[P[_]](i: Iterable[(P[_], MultiSet[_])]) {
    def toMarking: Marking[P] = HMap[P, MultiSet](i.toMap[P[_], MultiSet[_]])
  }

  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking

  implicit class MultiSetToMarking[P[_]](m: MultiSet[P[_]]) {
    def toMarking: Marking[P] = m.map { case (p, n) ⇒ p -> Map(() -> n) }.toMarking
  }
}
