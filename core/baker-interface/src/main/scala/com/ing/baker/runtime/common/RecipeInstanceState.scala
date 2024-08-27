package com.ing.baker.runtime.common

import com.ing.baker.il.recipeInstanceMetadataName
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Value

object RecipeInstanceState {
  //The name used for the RecipeInstanceMetaData ingredient
  val RecipeInstanceMetadataName = recipeInstanceMetadataName
}

/**
  * Holds the 'state' of a process instance.
  */
trait RecipeInstanceState extends LanguageApi { self =>

  type EventType <: EventMoment { type Language <: self.Language}

  def recipeId: String

  def recipeInstanceId: String

  def ingredients: language.Map[String, Value]

  def recipeInstanceMetadata: language.Map[String, String]

  def events: language.Seq[EventType]
}