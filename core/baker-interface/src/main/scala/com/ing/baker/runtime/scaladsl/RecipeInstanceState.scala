package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.Value

import scala.collection.immutable.Seq
import scala.collection.JavaConverters._

/**
  * Holds the 'state' of a process instance.
  *
  * @param recipeInstanceId   The process identifier
  * @param ingredients The accumulated ingredients
  * @param events  The events that have occurred so far
  */
case class RecipeInstanceState(
    recipeInstanceId: String,
    ingredients: Map[String, Value],
    events: Seq[EventMoment])
  extends common.RecipeInstanceState with ScalaApi {

  type EventType = EventMoment

  def eventNames: Seq[String] = events.map(_.name)

  def asJava: javadsl.RecipeInstanceState =
    new javadsl.RecipeInstanceState(recipeInstanceId, ingredients.asJava, events.map(_.asJava()).asJava)
}
