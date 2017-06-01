package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common

case class Interaction(override val name: String,
                       override val inputIngredients: Seq[Ingredient[_]],
                       interactionOutput: InteractionOutput)
  extends common.Interaction{

  override val output: Either[Seq[common.Event], common.Ingredient] = {
    interactionOutput match {
      case FiresOneOfEvents(events: Event) => Left(Seq(events))
      case ProvidesIngredient(ingredient) => Right(ingredient)
    }
  }
}

sealed trait InteractionOutput
case class FiresOneOfEvents(events: Event*) extends InteractionOutput
case class ProvidesIngredient(ingredient: Ingredient[_]) extends InteractionOutput