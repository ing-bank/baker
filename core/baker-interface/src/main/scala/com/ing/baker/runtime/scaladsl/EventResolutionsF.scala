package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi

trait EventResolutionsF[F[_]] extends common.EventResolutions[F] with ScalaApi {

  type SensoryEventResultType = SensoryEventResult
}
