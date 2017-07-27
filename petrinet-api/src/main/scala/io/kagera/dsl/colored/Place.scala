package io.kagera.dsl.colored

import io.kagera.api.{MarkedPlace, MultiSet}

object Place {
  def apply[Color](id: Long): Place[Color] = Place(id, s"p$id")
}

/**
 * A Place in a colored petri net.
 */
case class Place[Color](id: Long, label: String) {

  def apply[T <: Color](tokens: T*): MarkedPlace[Place, Color] = (this, MultiSet.copyOff(tokens))
}