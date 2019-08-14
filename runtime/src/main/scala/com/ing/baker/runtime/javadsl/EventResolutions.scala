package com.ing.baker.runtime.javadsl

import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi

class EventResolutions(
                        override val resolveWhenReceived: CompletableFuture[SensoryEventStatus],
                        override val resolveWhenCompleted: CompletableFuture[EventResult]
) extends common.EventResolutions[CompletableFuture] with JavaApi {

  type Result = EventResult
}
