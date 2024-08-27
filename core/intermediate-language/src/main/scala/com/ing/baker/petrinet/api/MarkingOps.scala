package com.ing.baker.petrinet.api

trait MarkingOps {

  /**
   * Some convenience method additions to work with Markings.
   */
  implicit class MarkingFunctions[X](marking: Marking[X]) {

    def multiplicities: MultiSet[X] = marking.view.map { case (key, value) => (key, value.multisetSize)}.toMap

    def add(p: X, value: Any, count: Int = 1): Marking[X] = {
      val newTokens = marking.getOrElse(p, MultiSet.empty).multisetIncrement(value, count)
      marking.+(p -> newTokens)
    }

    def |-|(other: Marking[X]): Marking[X] = other.keySet.foldLeft(marking) {

      case (result, place) =>

        marking.get(place) match {
          case None => result
          case Some(tokens) =>
            val newTokens = tokens.multisetDifference(other(place))
            if (newTokens.isEmpty)
              result - place
            else
              result + (place -> newTokens)
        }
    }

    def |+|(other: Marking[X]): Marking[X] = other.keySet.foldLeft(marking) {
      case (result, place) =>
        val newTokens = marking.get(place) match {
          case None         => other(place)
          case Some(tokens) => tokens.multisetSum(other(place))
        }

        result + (place -> newTokens)
    }
  }

  implicit class IterableToMarking[X](i: Iterable[(X, MultiSet[Any])]) {
    def toMarking: Marking[X] = i.toMap[X, MultiSet[Any]]
  }

  /**
    * maps a MultiSet of Places to a Marking with always null values.<br>
    * Having null values here is due to the design of petrinet library which uses a ColoredPetriNet which supports tokens with values.<br>
    * Here we only know the Place and the number of tokens, but not the values, so the value is initialized to null.
    * @param mset MultiSet of Places
    * @tparam X Place type parameter
    * @return Marking (state of the petrinet) with 'null' token values
    */
  implicit class MultiSetToMarking[X](mset: MultiSet[X]) {
    def toMarking: Marking[X] = mset.map { case (p, n) => p -> Map[Any, Int](Tuple2(null, n)) }.toMarking
  }
}
