package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus

abstract class EventResolutionsF[F[_]](
                             val resolveWhenReceivedF: F[SensoryEventStatus],
                             val resolveWhenCompletedF: F[SensoryEventResult]
                           ) extends common.EventResolutions[F] with ScalaApi {

  type SensoryEventResultType = SensoryEventResult
}
