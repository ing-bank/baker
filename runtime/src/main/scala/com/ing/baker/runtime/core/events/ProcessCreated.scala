package com.ing.baker.runtime.core.events

case class ProcessCreated(timeStamp: Long,
                          recipeId: String,
                          recipeName: String,
                          processId: String) extends BakerEvent
