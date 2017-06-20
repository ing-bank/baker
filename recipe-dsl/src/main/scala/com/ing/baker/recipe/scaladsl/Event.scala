package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

case class Event (override val name: String,
                  override val providedIngredients: Seq[common.Ingredient]) extends common.Event

object Event {
  def apply(name: String) : Event = Event(name, Seq.empty)

  def apply(name: String, ingredientOne: Ingredient[_]) : Event =
    Event(name, Seq(ingredientOne))

  def apply(name: String, ingredientOne: Ingredient[_], ingredientTwo: Ingredient[_]) : Event =
    Event(name, Seq(ingredientOne, ingredientTwo))

  def apply(name: String, ingredientOne: Ingredient[_], ingredientTwo: Ingredient[_], ingredientThree: Ingredient[_]) : Event =
    Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree))

  def apply(name: String, ingredientOne: Ingredient[_], ingredientTwo: Ingredient[_], ingredientThree: Ingredient[_], ingredientFour: Ingredient[_]) : Event =
    Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree, ingredientFour))

  def apply(name: String, ingredientOne: Ingredient[_], ingredientTwo: Ingredient[_], ingredientThree: Ingredient[_], ingredientFour: Ingredient[_], ingredientFive: Ingredient[_]) : Event =
    Event(name, Seq(ingredientOne, ingredientTwo, ingredientThree, ingredientFour, ingredientFive))
}
