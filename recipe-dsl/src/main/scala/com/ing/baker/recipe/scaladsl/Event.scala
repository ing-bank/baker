package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

case class Event (override val name: String,
                  override val providedIngredients: Seq[common.Ingredient],
                  override val maxFiringLimit: Option[Integer]) extends common.Event {
  def withMaxFiringLimit(firingLimit: Integer): Event = {
    Event(this.name, this.providedIngredients, Some(firingLimit))
  }
}

object Event {
  def apply(name: String) : Event = new Event(name, Seq.empty, Some(1))

  def apply(name: String, ingredients: common.Ingredient*) : Event =
    new Event(name, ingredients, Some(1))
}
