package com.ing.baker.baas.protocol

import com.ing.baker.runtime.common.{EventInstance, InteractionInstance, RecipeEventMetadata}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait BaaSEventListener[F[_]] extends LanguageApi { self =>

  type EventInstanceType <: EventInstance { type Language <: self.Language }

  type RecipeEventMetadataType <: RecipeEventMetadata { type Language <: self.Language }

  def registerEventListener(recipeName: String, listenerFunction: language.BiConsumerFunction[RecipeEventMetadataType, EventInstanceType]): F[Unit]

}
