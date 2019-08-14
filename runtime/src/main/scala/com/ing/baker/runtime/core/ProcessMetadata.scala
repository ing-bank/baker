package com.ing.baker.runtime.core

/**
  * This class holds some meta data of a baker process.
  *
  * @param recipeId The recipe id of the process
  * @param processId The identifier of the process
  * @param createdTime The time the process was created
  */
case class ProcessMetadata(recipeId: String, processId: String, createdTime: Long) {

  /**
    * Returns the recipe id of the process.
    *
    * @return The recipe id of the process.
    */
  def getRecipeId(): String  = recipeId

  /**
    * Returns the process identifier.
    *
    * @return The process identifier.
    */
  def getProcessId(): String = processId

  /**
    * Returns the time the process was created.
    *
    * The timestamp is measured as the difference, in milliseconds, between
    * the process created time and midnight, January 1, 1970 UTC.
    *
    * @return The time the process was created.
    */
  def getCreatedTime(): Long = createdTime
}
