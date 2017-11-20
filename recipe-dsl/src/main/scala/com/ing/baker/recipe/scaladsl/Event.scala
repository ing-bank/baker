package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

import scala.language.experimental.macros

case class Event (override val name: String,
                  override val providedIngredients: Seq[common.Ingredient],
                  override val maxFiringLimit: Option[Integer]) extends common.Event {
  def withMaxFiringLimit(firingLimit: Integer): Event = {
    Event(this.name, this.providedIngredients, Some(firingLimit))
  }
}

object Event {
  def apply(ingredients: common.Ingredient*) : Event = macro CommonMacros.eventImpl

  def apply(name: String, ingredients: common.Ingredient*) : Event =
    new Event(name, ingredients, Some(1))
}
