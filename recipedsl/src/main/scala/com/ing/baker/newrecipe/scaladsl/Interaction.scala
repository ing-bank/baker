package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common

case class Interaction(override val name: String,
                       interactionOutput: InteractionOutput,
                       override val inputIngredients: Seq[Ingredient[_]])
  extends common.Interaction{

  override val output: Either[Seq[common.Event], common.Ingredient] = {
    interactionOutput match {
      case FiresOneOfEvents(events: Seq[Event]) => Left(events)
      case ProvidesIngredient(ingredient) => Right(ingredient)
    }
  }
}

sealed trait InteractionOutput{
  def toString(appender: String): String
}
case class FiresOneOfEvents(events: Seq[Event]) extends InteractionOutput {

  override def toString(): String = toString("")

  def toString(appender: String): String = {
    s"""${appender}FiresOneOfEvents:{
       |${events.foldLeft("")((i, j) => s"$i\n${appender + "  "}$j").replaceFirst("\n", "")}}""".stripMargin
  }
}
case class ProvidesIngredient(ingredient: Ingredient[_]) extends InteractionOutput {
  override def toString(): String = toString("")

  def toString(appender: String): String = {
    s"""${appender}ProvidesIngredient($ingredient)""".stripMargin

  }
}
