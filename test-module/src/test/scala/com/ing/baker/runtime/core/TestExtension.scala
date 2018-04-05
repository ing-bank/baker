package com.ing.baker.runtime.core

import com.ing.baker.types.Value

class TestExtension extends BakerExtension {
  override def onBake(recipeId: String, processId: String): Unit =
    println(s"recipe '$recipeId' baked with processId: '$processId")

  override def onEventReceived(processId: String, event: RuntimeEvent): Unit =
    println(s"[$processId] event received: $event")

  override def onInteractionCalled(processId: String, interactionName: String, ingredients: Seq[(String, Value)]): Unit =
    println(s"[$processId] interaction '$interactionName' called with arguments: " +
      ingredients.map { case (name, value) => s"$name: $value"}.mkString("[", ",", "]"))

  override def onInteractionFinished(processId: String, interactionName: String, event: RuntimeEvent): Unit =
    println(s"[$processId] interaction '$interactionName' finished with output: $event")

  override def onInteractionFailed(processId: String, interactionName: String, throwable: Throwable): Unit =
    println(s"[$processId] interaction '$interactionName' failed with $throwable")
}