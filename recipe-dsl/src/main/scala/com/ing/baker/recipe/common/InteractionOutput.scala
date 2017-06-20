package com.ing.baker.recipe.common

sealed trait InteractionOutput

case class ProvidesIngredient(ingredient: Ingredient) extends InteractionOutput {
  override def toString(): String = toString("")
  def toString(appender: String): String = {
    s"""${appender}ProvidesIngredient($ingredient)""".stripMargin
  }
}

case class FiresOneOfEvents(events: Seq[Event]) extends InteractionOutput {
  override def toString(): String = {
    s"""FiresOneOfEvents:{
       |${events.mkString("\n")}}""".stripMargin
  }
}

object FiresOneOfEvents {
  def apply(event: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(event))
  def apply(eventOne: Event, eventTwo: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event, eventFour: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree, eventFour))
  def apply(eventOne: Event, eventTwo: Event, eventThree: Event, eventFour: Event, eventFive: Event): FiresOneOfEvents = FiresOneOfEvents(Seq(eventOne, eventTwo, eventThree, eventFour, eventFive))
}

case class ProvidesNothing() extends InteractionOutput {
  override def toString(): String = "ProvidesNothing:"
}