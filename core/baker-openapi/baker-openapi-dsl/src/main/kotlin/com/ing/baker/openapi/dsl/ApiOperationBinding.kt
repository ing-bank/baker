package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.InteractionInstance
import community.flock.wirespec.kotlin.Wirespec
import kotlin.reflect.KClass

/**
 * Pairs an [ApiOperation] descriptor with the wirespec handler that knows how to
 * execute it, plus the status → event mappers from the recipe. Produces an
 * [InteractionInstance] for Baker to register at startup.
 *
 * Mappers normally mirror those configured in the recipe's `api(...)` block.
 * [nameOverrides] map API field names to recipe ingredient names; the runtime
 * reverses the map to translate IngredientInstance names back to the API names
 * before invoking [ApiOperation.buildRequest].
 *
 * When the recipe used the typed `inputFrom<E, R>(mapper)` flow,
 * [inputEventClass] and [inputMapper] are set: the runtime reconstructs an [E]
 * instance from ingredients and applies [inputMapper] to produce the wirespec
 * body DTO, which the descriptor wraps via [ApiOperation.buildRequestFromBody].
 */
class ApiOperationBinding(
    private val operation: ApiOperation<*>,
    private val handler: Wirespec.Handler,
    private val mappers: Map<Int, (Wirespec.Response<*>) -> Any>,
    private val nameOverrides: Map<String, String> = emptyMap(),
    private val inputEventClass: KClass<*>? = null,
    private val inputMapper: ((Any) -> Any)? = null,
) {
    fun toInteractionInstance(): InteractionInstance =
        ApiOperationInteraction(operation, handler, mappers, nameOverrides, inputEventClass, inputMapper)
}
