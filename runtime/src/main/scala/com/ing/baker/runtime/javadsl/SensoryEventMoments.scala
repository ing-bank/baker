package com.ing.baker.runtime.javadsl

import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.common

class SensoryEventMoments(
  override val received: CompletableFuture[SensoryEventStatus],
  override val completed: CompletableFuture[SensoryEventResult]
) extends common.SensoryEventMoments[CompletableFuture, java.util.List, java.util.Map, SensoryEventResult]
