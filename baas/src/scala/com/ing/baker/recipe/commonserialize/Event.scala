package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common

case class Event (override val name: String,
                  override val providedIngredients: Seq[Ingredient],
                  override val maxFiringLimit: Option[Integer]) extends common.Event {

  def this(event: common.Event) =
    this(
      event.name,
      event.providedIngredients.map(i => new Ingredient(i)),
      event.maxFiringLimit)
}
