package com.ing.baker.petrinet.api

trait MarkingOps {

  /**
   * Some convenience method additions to work with Markings.
   */
  implicit class MarkingFunctions[P](marking: Marking[P]) {

    // Note: extra .map(identity) is a needed to workaround the scala Map serialization bug: https://issues.scala-lang.org/browse/SI-7005
    def multiplicities: MultiSet[P] = marking.mapValues(_.multisetSize).map(identity)

    def add(p: P, value: Any, count: Int = 1): Marking[P] = {
      val newTokens = marking.getOrElse(p, MultiSet.empty).multisetIncrement(value, count)
      marking.+(p -> newTokens)
    }

    def |-|(other: Marking[P]): Marking[P] = other.keySet.foldLeft(marking) {

      case (result, place) ⇒

        marking.get(place) match {
          case None ⇒ result
          case Some(tokens) ⇒
            val newTokens = tokens.multisetDifference(other(place))
            if (newTokens.isEmpty)
              result - place
            else
              result + (place -> newTokens)
        }
    }

    def |+|(other: Marking[P]): Marking[P] = other.keySet.foldLeft(marking) {
      case (result, place) ⇒
        val newTokens = marking.get(place) match {
          case None         ⇒ other(place)
          case Some(tokens) ⇒ tokens.multisetSum(other(place))
        }

        result + (place -> newTokens)
    }
  }

  implicit class IterableToMarking[P](i: Iterable[(P, MultiSet[Any])]) {
    def toMarking: Marking[P] = i.toMap[P, MultiSet[Any]]
  }

  /**
    * maps a MultiSet of Places to a Marking with always null values.<br>
    * Having null values here is due to the design of petrinet library which uses a ColoredPetriNet which supports tokens with values.<br>
    * Here we only know the Place and the number of tokens, but not the values, so the value is initialized to null.
    * @param mset MultiSet of Places
    * @tparam P Place type parameter
    * @return Marking (state of the petrinet) with 'null' token values
    */
  implicit class MultiSetToMarking[P](mset: MultiSet[P]) {
    def toMarking: Marking[P] = mset.map { case (p, n) ⇒ p -> Map[Any, Int](Tuple2(null, n)) }.toMarking
  }
}
