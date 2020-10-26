package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.SensoryEventStatus

import scala.concurrent.Future

case class EventResolutions(
                             resolveWhenReceived: Future[SensoryEventStatus],
                             resolveWhenCompleted: Future[SensoryEventResult]
) extends EventResolutionsF[Future](resolveWhenReceived, resolveWhenCompleted)

