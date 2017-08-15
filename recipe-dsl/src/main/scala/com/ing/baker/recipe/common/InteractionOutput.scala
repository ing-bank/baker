package com.ing.baker.recipe.common

sealed trait InteractionOutput

case class ProvidesIngredient(ingredient: Ingredient) extends InteractionOutput

case class FiresOneOfEvents(events: Event*) extends InteractionOutput

case object ProvidesNothing extends InteractionOutput