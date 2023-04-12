package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.javadsl.SensoryEventResult
import kotlinx.coroutines.Deferred

data class EventResolutions(
    val resolveWhenReceived: Deferred<SensoryEventStatus>,
    val resolveWhenCompleted: Deferred<SensoryEventResult>
)