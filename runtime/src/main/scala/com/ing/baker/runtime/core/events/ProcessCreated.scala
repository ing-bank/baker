package com.ing.baker.runtime.core.events

/**
  * Event describing the fact that a baker process was created
  *
  * @param timeStamp The time the process was created
  * @param recipeId The recipe id
  * @param recipeName The name of the recipe
  * @param processId The process id
  */
case class ProcessCreated(timeStamp: Long,
                          recipeId: String,
                          recipeName: String,
                          processId: String) extends BakerEvent
