package com.ing.baker.runtime.core

import com.ing.baker.types.Value

class TestExtension extends BakerExtension {
  override def onBake(recipeId: String, processId: String): Unit =
    println("onBake")

  override def onEventReceived(processId: String, event: RuntimeEvent): Unit =
    println("onEventReceived")

  override def onInteractionCalled(processId: String, interactionName: String, ingredients: Seq[(String, Value)]): Unit =
    println("onInteractionCalled")

  override def onInteractionFinished(processId: String, interactionName: String, event: RuntimeEvent): Unit =
    println("onInteractionFinished")

  override def onInteractionFailed(processId: String, interactionName: String, throwable: Throwable): Unit =
    println("onInteractionFailed")
}