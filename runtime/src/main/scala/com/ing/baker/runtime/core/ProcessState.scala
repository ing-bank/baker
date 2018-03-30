package com.ing.baker.runtime.core

import com.ing.baker.types.Value

import scala.collection.JavaConverters._

/**
  * Describes the state of a process
  *
  * @param processId The process identifier
  * @param ingredients The collected ingredients
  * @param eventNames A list names of the event that occurred
  */
case class ProcessState(processId: String, ingredients: Map[String, Value], eventNames: List[String]) extends Serializable {

  def getIngredients(): java.util.Map[String, Value] = ingredients.asJava

  def getEventNames(): java.util.List[String] = eventNames.asJava

  def getProcessId(): String = processId
}