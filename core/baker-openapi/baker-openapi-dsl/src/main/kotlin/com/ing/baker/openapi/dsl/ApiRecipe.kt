package com.ing.baker.openapi.dsl

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.Recipe
import com.ing.baker.recipe.kotlindsl.RecipeBuilder
import com.ing.baker.runtime.javadsl.InteractionInstance
import community.flock.wirespec.kotlin.Wirespec

/**
 * A [Recipe] paired with the response mappers configured by `api(...) { on(...) { ... } }`
 * blocks. The mappers are the recipe's responsibility — startup code only needs to
 * supply the underlying wirespec handlers.
 */
class ApiRecipe internal constructor(
    val recipe: Recipe,
    internal val mappersByOperation: Map<String, Pair<ApiOperation, Map<Int, (Wirespec.Response<*>) -> Any>>>,
) {
    /**
     * Builds an [InteractionInstance] for every API operation in the recipe using
     * the supplied [transport] and [serialization]. Every descriptor knows how to
     * build its own wirespec handler — callers register nothing per operation.
     */
    fun toInteractionInstances(
        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,
        serialization: Wirespec.Serialization,
    ): List<InteractionInstance> =
        mappersByOperation.values.map { (op, mappers) ->
            val handler = op.buildHandler(transport, serialization)
            ApiOperationBinding(op, handler, mappers).toInteractionInstance()
        }

    /**
     * Overload for callers who want to supply a handler explicitly per operation
     * (e.g. tests with custom fakes). Operations not in [handlers] fall back to
     * the descriptor's default handler built from (transport, serialization).
     */
    fun toInteractionInstances(
        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,
        serialization: Wirespec.Serialization,
        overrides: Map<ApiOperation, Wirespec.Handler>,
    ): List<InteractionInstance> =
        mappersByOperation.values.map { (op, mappers) ->
            val handler = overrides[op] ?: op.buildHandler(transport, serialization)
            ApiOperationBinding(op, handler, mappers).toInteractionInstance()
        }
}

/**
 * Builds an [ApiRecipe] — same shape as `recipe(name) { ... }` but the returned
 * wrapper carries the response mappers configured inside `api(...)` blocks so the
 * runtime can construct interaction instances without re-declaring them.
 */
@OptIn(ExperimentalDsl::class)
fun apiRecipe(name: String, configure: RecipeBuilder.() -> Unit): ApiRecipe {
    val collector = mutableMapOf<String, Pair<ApiOperation, Map<Int, (Wirespec.Response<*>) -> Any>>>()
    apiMappersCollector.set(collector)
    try {
        val recipe = com.ing.baker.recipe.kotlindsl.recipe(name, configure)
        return ApiRecipe(recipe, collector.toMap())
    } finally {
        apiMappersCollector.remove()
    }
}

internal val apiMappersCollector: ThreadLocal<MutableMap<String, Pair<ApiOperation, Map<Int, (Wirespec.Response<*>) -> Any>>>?> =
    ThreadLocal.withInitial { null }
