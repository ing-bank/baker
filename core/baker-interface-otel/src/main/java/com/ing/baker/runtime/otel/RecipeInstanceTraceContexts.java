package com.ing.baker.runtime.otel;

import io.opentelemetry.context.Context;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Keeps the tracing context that interaction spans of a recipe instance should be parented to.
 *
 * <p>Each Baker runtime owns its own instance, so contexts never leak between bakers, and entries are
 * removed as soon as the recipe instance is done.
 */
public final class RecipeInstanceTraceContexts {

    private final Map<String, Context> contexts = new ConcurrentHashMap<>();

    public void put(String recipeInstanceId, Context context) {
        if (recipeInstanceId == null || context == null) {
            return;
        }
        contexts.put(recipeInstanceId, context);
    }

    /**
     * Returns the parent context for the given recipe instance, falling back to the context currently
     * attached to the calling thread.
     */
    public Context parentOf(String recipeInstanceId) {
        final Context context = recipeInstanceId == null ? null : contexts.get(recipeInstanceId);
        return context != null ? context : Context.current();
    }

    public void remove(String recipeInstanceId) {
        if (recipeInstanceId != null) {
            contexts.remove(recipeInstanceId);
        }
    }

    public void clear() {
        contexts.clear();
    }
}
