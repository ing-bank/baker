package com.ing.baker.baas.protocol

import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}

sealed trait ProtocolDistributedEventPublishing

object ProtocolDistributedEventPublishing {

  case class Event(recipeEventMetadata: RecipeEventMetadata, event: EventInstance) extends ProtocolDistributedEventPublishing
}
