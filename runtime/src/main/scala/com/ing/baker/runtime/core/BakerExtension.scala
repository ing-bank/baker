package com.ing.baker.runtime.core

import com.ing.baker.types.Value

trait BakerExtension {

  def onBake(recipeId: String, processId: String)

  def onEventReceived(processId: String, event: RuntimeEvent)

  /**
    * Called just before an interaction is executed on the same thread.
    *
    * ? Should we allow implementers to throw in exception to prevent interaction execution
    *
    * This would allow some sort of ingredient validation extension.
    *
    * @param processId
    * @param interactionName
    * @param ingredients
    */
  def onInteractionCalled(processId: String, interactionName: String, ingredients: Seq[(String, Value)])

  /**
    * Called just after an interaction was executed on the same thread.
    *
    *
    *
    * @param processId
    * @param interactionName
    * @param event
    */
  def onInteractionFinished(processId: String, interactionName: String, event: RuntimeEvent)

  def onInteractionFailed(processId: String, interactionName: String, throwable: Throwable)
}
