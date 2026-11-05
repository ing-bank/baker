package com.ing.baker.runtime.model;

import com.ing.baker.runtime.model.propagation.ContextScope;
import org.slf4j.MDC;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Installs the diagnostic context of a single interaction invocation on the current thread.
 *
 * <p>This is applied on the thread that actually invokes the interaction, which makes it independent of how a
 * runtime composes its effects: an effect type that only builds a description on the calling thread (such as
 * {@code cats.effect.IO}) would otherwise lose a diagnostic context installed by the caller.
 */
public final class InteractionMdc {

    private static final String[] KEYS = {
            "recipeInstanceId",
            "recipeName",
            "baker.recipe.instance.id",
            "baker.recipe.name",
            "baker.recipe.id",
            "baker.interaction.name"
    };

    private InteractionMdc() {
    }

    /**
     * Sets the interaction MDC keys and returns a scope restoring the previous values.
     */
    public static ContextScope install(InteractionCallContext context) {
        if (context == null) {
            return ContextScope.NOOP;
        }
        final Map<String, String> previous = new LinkedHashMap<>();
        for (String key : KEYS) {
            previous.put(key, MDC.get(key));
        }
        try {
            MDC.put("recipeInstanceId", context.getRecipeInstanceId());
            MDC.put("recipeName", context.getRecipeName());
            MDC.put("baker.recipe.instance.id", context.getRecipeInstanceId());
            MDC.put("baker.recipe.name", context.getRecipeName());
            MDC.put("baker.recipe.id", context.getRecipeId());
            MDC.put("baker.interaction.name", context.getInteractionName());
        } catch (Throwable ignored) {
            // Diagnostics must never break an interaction.
        }
        return () -> {
            for (Map.Entry<String, String> entry : previous.entrySet()) {
                if (entry.getValue() == null) {
                    MDC.remove(entry.getKey());
                } else {
                    MDC.put(entry.getKey(), entry.getValue());
                }
            }
        };
    }
}
