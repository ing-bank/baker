package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

import scala.language.experimental.macros

object Event {
  def apply(ingredients: common.Ingredient*) : Event = macro CommonMacros.eventImpl

  def apply(name: String, ingredients: common.Ingredient*) : Event =
    new Event(name, ingredients, Some(1))
}

case class Event (override val name: String,
                  override val providedIngredients: Seq[common.Ingredient],
                  override val maxFiringLimit: Option[Int]) extends common.Event {
  def withMaxFiringLimit(firingLimit: Int): Event = {
    Event(this.name, this.providedIngredients, Some(firingLimit))
  }
}