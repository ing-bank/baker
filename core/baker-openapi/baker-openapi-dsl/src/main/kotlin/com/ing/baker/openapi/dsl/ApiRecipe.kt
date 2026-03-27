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
     * Builds an [InteractionInstance] for every operation declared in the recipe by
     * pairing each operation with its handler from [handlers]. Throws if any
     * operation lacks a handler.
     */
    fun toInteractionInstances(handlers: Map<ApiOperation, Wirespec.Handler>): List<InteractionInstance> =
        mappersByOperation.values.map { (op, mappers) ->
            val handler = handlers[op]
                ?: error("No handler provided for operation '${op.operationName}'. " +
                    "Pass it via handlers = mapOf(${op.operationName} to <handler>)")
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
