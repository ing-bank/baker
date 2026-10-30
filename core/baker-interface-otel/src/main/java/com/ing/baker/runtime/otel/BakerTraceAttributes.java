package com.ing.baker.runtime.otel;

/**
 * Attribute keys shared by all Baker OpenTelemetry instrumentation.
 */
public final class BakerTraceAttributes {

    public static final String RECIPE_ID = "baker.recipe.id";
    public static final String RECIPE_NAME = "baker.recipe.name";
    public static final String RECIPE_INSTANCE_ID = "baker.recipe.instance.id";
    public static final String EVENT_NAME = "baker.event.name";
    public static final String INTERACTION_NAME = "baker.interaction.name";
    public static final String CORRELATION_ID = "baker.correlation.id";
    public static final String FAILURE_COUNT = "baker.failure.count";
    public static final String ERROR_TYPE = "error.type";

    public static final String INTERACTION_FAILURE = "interaction.failure";

    private BakerTraceAttributes() {
    }
}
