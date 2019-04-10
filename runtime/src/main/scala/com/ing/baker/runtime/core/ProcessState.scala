package com.ing.baker.runtime.core

import com.ing.baker.types.{PrimitiveValue, Value}

import scala.collection.JavaConverters._

/**
  * Holds the 'state' of a process instance.
  *
  * @param processId   The process identifier
  * @param ingredients The accumulated ingredients
  * @param eventNames  The names of the events occurred so far
  */
case class ProcessState(processId: String,
                        ingredients: Map[String, Value],
                        eventNames: List[String]) extends Serializable {

  /**
    * Returns the accumulated ingredients.
    *
    * @return The accumulated ingredients
    */
  def getIngredients(): java.util.Map[String, Value] = ingredients.asJava

  /**
    * Returns the names of the events occurred so far.
    *
    * @return The names of the events occurred so far
    */
  def getEventNames(): java.util.List[String] = eventNames.asJava

  /**
    * Returns the process identifier.
    *
    * @return The process identifier
    */
  def getProcessId(): String = processId


  def filterIngredients(ingredientFilter: Seq[String]): ProcessState =
    copy(processId,
      ingredients.map(ingredient =>
        if (ingredientFilter.contains(ingredient._1))
          ingredient._1 -> PrimitiveValue("")
        else
          ingredient
      ), eventNames)

}