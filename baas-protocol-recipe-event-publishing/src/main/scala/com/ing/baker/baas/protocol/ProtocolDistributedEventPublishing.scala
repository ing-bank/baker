package com.ing.baker.baas.protocol

import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}

sealed trait ProtocolDistributedEventPublishing

object ProtocolDistributedEventPublishing {

  def eventsTopic(recipeName: String): String =
    s"recipe-event-publishing:$recipeName:event"

  case class Event(recipeEventMetadata: RecipeEventMetadata, event: EventInstance) extends ProtocolDistributedEventPublishing
}
