package com.ing.baker.baas.protocol

import com.ing.baker.runtime.common.InteractionInstance
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

trait BaaSInteractionInstance[F[_]] extends LanguageApi { self =>

  type InteractionInstanceType <: InteractionInstance[F] { type Language <: self.Language }

  def load(implementation: InteractionInstanceType*): Unit

}
