package com.ing.baker.openapi.dsl

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.Recipe
import com.ing.baker.recipe.kotlindsl.RecipeBuilder
import com.ing.baker.runtime.javadsl.InteractionInstance
import community.flock.wirespec.kotlin.Wirespec

/**
 * A [Recipe] paired with the per-operation configuration declared inside
 * `api(...) { ... }` blocks (response mappers, ingredient name overrides).
 * Startup code only needs to supply the transport + serialization.
 */
class ApiRecipe internal constructor(
    val recipe: Recipe,
    internal val configsByOperation: Map<String, ApiInteractionConfig>,
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
        configsByOperation.values.map { cfg ->
            val handler = cfg.operation.buildHandler(transport, serialization)
            ApiOperationBinding(cfg.operation, handler, cfg.mappers, cfg.nameOverrides).toInteractionInstance()
        }

    /**
     * Overload for callers who want to supply a handler explicitly per operation
     * (e.g. tests with custom fakes). Operations not in [overrides] fall back to
     * the descriptor's default handler built from (transport, serialization).
     */
    fun toInteractionInstances(
        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,
        serialization: Wirespec.Serialization,
        overrides: Map<ApiOperation, Wirespec.Handler>,
    ): List<InteractionInstance> =
        configsByOperation.values.map { cfg ->
            val handler = overrides[cfg.operation] ?: cfg.operation.buildHandler(transport, serialization)
            ApiOperationBinding(cfg.operation, handler, cfg.mappers, cfg.nameOverrides).toInteractionInstance()
        }
}

/**
 * Builds an [ApiRecipe] — same shape as `recipe(name) { ... }` but the returned
 * wrapper carries the configuration collected from `api(...)` blocks so the
 * runtime can construct interaction instances without re-declaring it.
 */
@OptIn(ExperimentalDsl::class)
fun apiRecipe(name: String, configure: RecipeBuilder.() -> Unit): ApiRecipe {
    val collector = mutableMapOf<String, ApiInteractionConfig>()
    apiInteractionConfigCollector.set(collector)
    try {
        val recipe = com.ing.baker.recipe.kotlindsl.recipe(name, configure)
        return ApiRecipe(recipe, collector.toMap())
    } finally {
        apiInteractionConfigCollector.remove()
    }
}

internal val apiInteractionConfigCollector: ThreadLocal<MutableMap<String, ApiInteractionConfig>?> =
    ThreadLocal.withInitial { null }
