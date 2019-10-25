package com.ing.baker.baas.common

import com.ing.baker.runtime.common.{EventInstance, InteractionInstance}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait BaaSEventListener[F[_]] extends LanguageApi { self =>

  type EventInstanceType <: EventInstance { type Language <: self.Language }

  def registerEventListener(recipeName: String, listenerFunction: language.BiConsumerFunction[String, EventInstanceType]): F[Unit]

}
