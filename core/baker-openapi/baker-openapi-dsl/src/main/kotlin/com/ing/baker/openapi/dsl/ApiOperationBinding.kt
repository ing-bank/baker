package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.InteractionInstance
import community.flock.wirespec.kotlin.Wirespec

/**
 * Pairs an [ApiOperation] descriptor with the wirespec handler that knows how to
 * execute it, plus the status → event mappers from the recipe. Produces an
 * [InteractionInstance] for Baker to register at startup.
 *
 * Mappers normally mirror those configured in the recipe's `api(...)` block.
 */
class ApiOperationBinding(
    private val operation: ApiOperation,
    private val handler: Wirespec.Handler,
    private val mappers: Map<Int, (Wirespec.Response<*>) -> Any>,
) {
    fun toInteractionInstance(): InteractionInstance =
        ApiOperationInteraction(operation, handler, mappers)
}
