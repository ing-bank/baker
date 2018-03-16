package com.ing.baker.runtime.core

/**
  * This class is to store some metadata information of a baker process
  *
  * @param recipeId is dof the process
  * @param processId id of the recipe
  * @param createdTime process created date-time
  */
case class ProcessMetadata(recipeId: String, processId: String, createdTime: Long) {

  def getRecipeId(): String  = recipeId

  def getProcessId(): String = processId

  def getCreatedTime(): Long = createdTime
}
