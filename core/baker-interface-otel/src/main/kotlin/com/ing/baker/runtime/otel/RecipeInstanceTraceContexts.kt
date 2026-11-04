package com.ing.baker.runtime.otel

import io.opentelemetry.context.Context
import java.util.concurrent.ConcurrentHashMap

/**
 * Keeps the tracing context that interaction spans of a recipe instance should be parented to.
 *
 * Each Baker runtime owns its own instance, so contexts never leak between bakers, and entries are
 * removed as soon as the recipe instance is done.
 */
class RecipeInstanceTraceContexts {

    private val contexts = ConcurrentHashMap<String, Context>()

    fun put(recipeInstanceId: String?, context: Context?) {
        if (recipeInstanceId != null && context != null) {
            contexts[recipeInstanceId] = context
        }
    }

    fun putIfAbsent(recipeInstanceId: String?, context: Context?) {
        if (recipeInstanceId != null && context != null) {
            contexts.putIfAbsent(recipeInstanceId, context)
        }
    }

    /**
     * Returns the parent context for the given recipe instance, falling back to the context currently
     * attached to the calling thread.
     */
    fun parentOf(recipeInstanceId: String?): Context {
        return if (recipeInstanceId != null) {
            contexts[recipeInstanceId] ?: Context.current()
        } else {
            Context.current()
        }
    }

    fun remove(recipeInstanceId: String?) {
        if (recipeInstanceId != null) {
            contexts.remove(recipeInstanceId)
        }
    }

    fun clear() {
        contexts.clear()
    }
}
