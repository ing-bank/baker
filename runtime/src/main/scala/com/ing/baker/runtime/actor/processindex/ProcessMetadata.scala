package com.ing.baker.runtime.actor.processindex

/**
  * This class is to store some metadata information of a baker process
  *
  * @param recipeId is dof the process
  * @param processId id of the recipe
  * @param createdTime process created date-time
  */
case class ProcessMetadata(recipeId: String, processId: String, createdTime: Long)
