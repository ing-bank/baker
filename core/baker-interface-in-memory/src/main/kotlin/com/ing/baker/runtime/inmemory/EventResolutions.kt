package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.javadsl.SensoryEventResult
import kotlinx.coroutines.Deferred

/**
 * Deferred resolutions for the deprecated callback-style fireEvent API.
 */
data class KotlinEventResolutions(
    val resolveWhenReceived: Deferred<SensoryEventStatus>,
    val resolveWhenCompleted: Deferred<SensoryEventResult>
)

