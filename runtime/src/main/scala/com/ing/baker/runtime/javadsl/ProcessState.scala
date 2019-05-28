package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

/**
  * Holds the 'state' of a process instance.
  *
  * @param processId   The process identifier
  * @param ingredients The accumulated ingredients
  * @param eventNames  The names of the events occurred so far
  */
class ProcessState(
    val processId: String,
    val ingredients: java.util.Map[String, Value],
    val eventNames: java.util.List[String]
  ) extends common.ProcessState with JavaApi {

  /**
    * Returns the accumulated ingredients.
    *
    * @return The accumulated ingredients
    */
  def getIngredients: java.util.Map[String, Value] = ingredients

  /**
    * Returns the names of the events occurred so far.
    *
    * @return The names of the events occurred so far
    */
  def getEventNames: java.util.List[String] = eventNames

  /**
    * Returns the process identifier.
    *
    * @return The process identifier
    */
  def getProcessId: String = processId

  def asScala: scaladsl.ProcessState =
    scaladsl.ProcessState(processId, ingredients.asScala.toMap, eventNames.asScala)
}
