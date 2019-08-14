package com.ing.baker.runtime.actor.process_instance.dsl

import com.ing.baker.petrinet.api._

object Place {
  def apply(id: Long): Place = Place(id, s"p$id")

  implicit val identifiable: Identifiable[Place] = p => p.id
}

/**
 * A Place in a colored petri net.
 */
case class Place(id: Long, label: String) {

  def apply(tokens: Any*): (Place, MultiSet[Any]) = (this, MultiSet.copyOff(tokens))

  def markWithN(n: Int): Marking[Place] =  Map[Place, MultiSet[Any]](this -> Map[Any, Int](Tuple2(null, n)))
}