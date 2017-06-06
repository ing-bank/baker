package com.ing.baker.newrecipe.common

sealed trait InteractionOutput {
  def toString(appender: String): String
}

case class ProvidesIngredient(ingredient: Ingredient) extends InteractionOutput {
  override def toString(): String = toString("")
  def toString(appender: String): String = {
    s"""${appender}ProvidesIngredient($ingredient)""".stripMargin
  }
}
case class FiresOneOfEvents(events: Seq[Event]) extends InteractionOutput {
  override def toString(): String = toString("")
  def toString(appender: String): String = {
    s"""${appender}FiresOneOfEvents:{
       |${events.foldLeft("")((i, j) => s"$i\n${j.toString(appender + "  ")}").replaceFirst("\n", "")}}""".stripMargin
  }
}
case object ProvidesNothing extends InteractionOutput {
  override def toString(): String = toString("")
  def toString(appender: String): String = {
    s"""${appender}ProvidesNothing:""".stripMargin
  }
}