package com.ing.baker.runtime.scaladsl

import cats.~>
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus

trait EventResolutionsF[F[_]] extends common.EventResolutions[F] with ScalaApi { self =>

  type SensoryEventResultType = SensoryEventResult

  def translate[G[_]](mapK: F ~> G): EventResolutionsF[G] =
    new EventResolutionsF[G] {
      override def resolveWhenReceived: G[SensoryEventStatus] =
        mapK(self.resolveWhenReceived)
      override def resolveWhenCompleted: G[SensoryEventResultType] =
        mapK(self.resolveWhenCompleted)
    }
}
