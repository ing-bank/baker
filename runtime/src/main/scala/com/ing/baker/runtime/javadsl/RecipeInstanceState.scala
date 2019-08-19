package com.ing.baker.runtime.javadsl

import java.util.stream.Collectors

import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

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
    ingredients: java.util.Map[String, Value],
    events: java.util.List[EventMoment]
  ) extends common.RecipeInstanceState with JavaApi {

  type EventType = EventMoment

  /**
    * Returns the accumulated ingredients.
    *
    * @return The accumulated ingredients
    */
  def getIngredients: java.util.Map[String, Value] = ingredients

  /**
    * Returns the RuntimeEvents
    *
    * @return The events occurred so far
    */
  def getEvents: java.util.List[EventMoment] = events

  /**
    * Returns the names of the events occurred so far.
    *
    * @return The names of the events occurred so far
    */
  def getEventNames: java.util.List[String] = events.stream().map[String](_.name).collect(Collectors.toList[String])

  /**
    * Returns the process identifier.
    *
    * @return The process identifier
    */
  def getRecipeInstanceId: String = recipeInstanceId

  def asScala: scaladsl.RecipeInstanceState =
    scaladsl.RecipeInstanceState(recipeInstanceId, ingredients.asScala.toMap, events.asScala.map(_.asScala))
}
