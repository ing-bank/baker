package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

class ProcessMetadata(val recipeId: String, val recipeInstanceId: String, val createdTime: Long) extends common.ProcessMetadata with JavaApi {

  /**
    * Returns the recipe id of the process.
    *
    * @return The recipe id of the process.
    */
  def getRecipeId: String  = recipeId

  /**
    * Returns the process identifier.
    *
    * @return The process identifier.
    */
  def getrecipeInstanceId: String = recipeInstanceId

  /**
    * Returns the time the process was created.
    *
    * The timestamp is measured as the difference, in milliseconds, between
    * the process created time and midnight, January 1, 1970 UTC.
    *
    * @return The time the process was created.
    */
  def getCreatedTime: Long = createdTime

  def asScala: scaladsl.ProcessMetadata =
    scaladsl.ProcessMetadata(recipeId, recipeInstanceId, createdTime)
}
