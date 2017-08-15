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

  def apply(name: String, ingredientOne: common.Ingredient) : Event =
    new Event(name, Seq(ingredientOne), Some(1))

  def apply(name: String, ingredientOne: common.Ingredient, ingredientTwo: common.Ingredient) : Event =
    new Event(name, Seq(ingredientOne, ingredientTwo),Some(1))

  def apply(name: String, ingredientOne: common.Ingredient, ingredientTwo: common.Ingredient, ingredientThree: common.Ingredient) : Event =
    new Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree), Some(1))

  def apply(name: String, ingredientOne: common.Ingredient, ingredientTwo: common.Ingredient, ingredientThree: common.Ingredient, ingredientFour: common.Ingredient) : Event =
    new Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree, ingredientFour),Some(1))

  def apply(name: String, ingredientOne: common.Ingredient, ingredientTwo: common.Ingredient, ingredientThree: common.Ingredient, ingredientFour: common.Ingredient, ingredientFive: common.Ingredient) : Event =
    new Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree, ingredientFour, ingredientFive),Some(1))
}
