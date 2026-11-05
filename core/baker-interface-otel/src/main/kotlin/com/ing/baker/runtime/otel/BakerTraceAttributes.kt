package com.ing.baker.runtime.otel

/**
 * Attribute keys shared by all Baker OpenTelemetry instrumentation.
 */
object BakerTraceAttributes {

    const val RECIPE_ID = "baker.recipe.id"
    const val RECIPE_NAME = "baker.recipe.name"
    const val RECIPE_INSTANCE_ID = "baker.recipe.instance.id"
    const val EVENT_NAME = "baker.event.name"
    const val INTERACTION_NAME = "baker.interaction.name"
    const val CORRELATION_ID = "baker.correlation.id"
    const val FAILURE_COUNT = "baker.failure.count"
    const val ERROR_TYPE = "error.type"

    const val INTERACTION_FAILURE = "interaction.failure"
}
