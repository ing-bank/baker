package com.ing.baker.baas.common

import com.ing.baker.runtime.common.{EventInstance, InteractionInstance, RecipeEventMetadata}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait RemoteEventListener[F[_]] extends LanguageApi { self =>

  type EventInstanceType <: EventInstance { type Language <: self.Language }

  type RecipeEventMetadataType <: RecipeEventMetadata { type Language <: self.Language }

  def load(listenerFunction: language.BiConsumerFunction[RecipeEventMetadataType, EventInstanceType]): Unit

}
