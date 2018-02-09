package com.ing.baker.petrinet.api

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

  /**
    * maps a tuple of (Place,NumberOfTokens) to a Marking with always null values.
    * See the javadoc of the toMarking function for the explanation of the null valued tokens.
    * @see com.ing.baker.petrinet.api.MarkingOps#toMarking
    * @param tuple Place -> NumberOfTokens tuple
    * @tparam P Place type parameter
    * @tparam C The color (type) of the place. The type of data that can be contained in that place.
    * @return MarkedPlace (Marking for a single place) with 'null' token values
    */
  implicit def toMarkedPlace[P[_], C](tuple: (P[C], Int)): MarkedPlace[P, C] = tuple._1 -> Map(Tuple2(null.asInstanceOf[C], tuple._2))

  implicit class IterableToMarking[P[_]](i: Iterable[(P[_], MultiSet[_])]) {
    def toMarking: Marking[P] = HMap[P, MultiSet](i.toMap[P[_], MultiSet[_]])
  }

  /**
    * maps a MultiSet of Places to a Marking with always null values.<br>
    * Having null values here is due to the design of petrinet library which uses a ColoredPetriNet which supports tokens with values.<br>
    * Here we only know the Place and the number of tokens, but not the values, so the value is initialized to null.
    * @param mset MultiSet of Places
    * @tparam P Place type parameter
    * @return Marking (state of the petrinet) with 'null' token values
    */
  def toMarking[P[_]](mset: MultiSet[P[_]]): Marking[P] = mset.map { case (p, n) ⇒ p -> Map(Tuple2(null, n)) }.toMarking

  implicit class MultiSetToMarking[P[_]](m: MultiSet[P[_]]) {
    def toMarking: Marking[P] = m.map { case (p, n) ⇒ p -> Map(Tuple2(null, n)) }.toMarking
  }
}
