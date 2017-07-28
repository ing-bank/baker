package com.ing.baker.petrinet.dsl.colored

import com.ing.baker.petrinet.api.{MarkedPlace, MultiSet}

object Place {
  def apply[Color](id: Long): Place[Color] = Place(id, s"p$id")
}

/**
 * A Place in a colored petri net.
 */
case class Place[Color](id: Long, label: String) {

  def apply[T <: Color](tokens: T*): MarkedPlace[Place, Color] = (this, MultiSet.copyOff(tokens))
}