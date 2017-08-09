package com.ing.baker.recipe.common

sealed trait InteractionOutput

case class ProvidesIngredient(ingredient: Ingredient) extends InteractionOutput

case class FiresOneOfEvents(events: Seq[Event]) extends InteractionOutput

object FiresOneOfEvents {
  def apply(event: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(event))
  def apply(eventOne: Event, eventTwo: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event, eventFour: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree, eventFour))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event, eventFour: Event, eventFive: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree, eventFour, eventFive))
}

case object ProvidesNothing extends InteractionOutput