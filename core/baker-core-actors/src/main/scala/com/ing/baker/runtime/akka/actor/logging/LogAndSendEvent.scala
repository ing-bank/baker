package com.ing.baker.runtime.akka.actor.logging

import com.ing.baker.runtime.common._
import com.ing.baker.runtime.model.BakerLogging

object LogAndSendEvent {

  val bakerLogging: BakerLogging = BakerLogging.default
  type PublishEvent = Any => Unit

  def recipeAdded(recipeAdded: RecipeAdded, publishEvent: PublishEvent): Unit = {
    publishEvent(recipeAdded)
    bakerLogging.addedRecipe(recipeAdded)
  }

  def recipeInstanceCreated(recipeInstanceCreated: RecipeInstanceCreated, publishEvent: PublishEvent): Unit = {
    publishEvent(recipeInstanceCreated)
    bakerLogging.recipeInstanceCreated(recipeInstanceCreated)
  }

  def interactionStarted(interactionStarted: InteractionStarted, publishEvent: PublishEvent): Unit = {
    publishEvent(interactionStarted)
    bakerLogging.interactionStarted(interactionStarted)
  }

  def interactionCompleted(interactionCompleted: InteractionCompleted, publishEvent: PublishEvent): Unit = {
    publishEvent(interactionCompleted)
    bakerLogging.interactionFinished(interactionCompleted)
  }

  def interactionFailed(interactionFailed: InteractionFailed, reason: Throwable, publishEvent: PublishEvent): Unit = {
    publishEvent(interactionFailed)
    bakerLogging.interactionFailed(interactionFailed, reason)
  }

  def eventReceived(eventReceived: EventReceived, publishEvent: PublishEvent): Unit = {
    publishEvent(eventReceived)
    bakerLogging.eventReceived(eventReceived)
  }

  def eventRejected(eventRejected: EventRejected, publishEvent: PublishEvent): Unit = {
    publishEvent(eventRejected)
    bakerLogging.eventRejected(eventRejected)
  }

  def eventFired(eventFired: EventFired,
                  publishEvent: PublishEvent): Unit = {
    publishEvent(eventFired)
    bakerLogging.eventFired(eventFired)
  }
}
