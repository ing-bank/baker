package com.ing.baker.petrinet.dsl.colored

import com.ing.baker.petrinet.api.{Id, Identifiable, MarkedPlace, Marking, MultiSet}

object Place {
  def apply(id: Long): Place = Place(id, s"p$id")

  implicit val identifiable: Identifiable[Place] = p => Id(p.id)
}

/**
 * A Place in a colored petri net.
 */
case class Place(id: Long, label: String) {

  def apply(tokens: Any*): MarkedPlace[Place] = (this, MultiSet.copyOff(tokens))

  def markWithN(n: Int): Marking[Place] = Marking(this -> Map[Any, Int](Tuple2(null, n)))
}