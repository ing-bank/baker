package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common

case class Event(override val name: String,
                 override val providedIngredients: Seq[Ingredient[_]])
  extends common.Event {

}

object Event {
  def apply(name: String) : Event = Event(name, Seq.empty)
}
