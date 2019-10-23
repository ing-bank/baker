package com.ing.baker.runtime.javadsl

import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

case class EventResolutions(resolveWhenReceived: CompletableFuture[SensoryEventStatus],
                            resolveWhenCompleted: CompletableFuture[SensoryEventResult]
) extends com.ing.baker.runtime.common.EventResolutions[CompletableFuture] with JavaApi {

  type SensoryEventResultType = SensoryEventResult

  def getResolveWhenReceived: CompletableFuture[SensoryEventStatus] = resolveWhenReceived

  def getResolveWhenCompleted: CompletableFuture[SensoryEventResult] = resolveWhenCompleted
}
