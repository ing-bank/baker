package com.ing.baker.runtime.otel

import com.ing.baker.runtime.model.TracingMdcRegistry
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.scaladsl.EventFired
import com.ing.baker.runtime.scaladsl.EventReceived
import com.ing.baker.runtime.scaladsl.RecipeInstanceCreated
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.context.Context
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import scala.runtime.AbstractFunction1
import scala.runtime.BoxedUnit

/**
 * Emits OpenTelemetry spans for the lifecycle and event [BakerEvent]s of a Baker runtime.
 *
 * Besides emitting spans this listener maintains the per recipe instance trace context that interaction spans
 * are parented to, so it must share its [RecipeInstanceTraceContexts] instance with the
 * [OpenTelemetryInteractionInstrumentation] of the same Baker.
 *
 * It is a `scala.Function1<BakerEvent, BoxedUnit>` so it can be handed directly to
 * `Baker.registerBakerEventListener`.
 */
class BakerEventTracingListener(
    private val tracer: Tracer,
    private val traceContexts: RecipeInstanceTraceContexts
) : AbstractFunction1<BakerEvent, BoxedUnit>() {

    override fun apply(event: BakerEvent): BoxedUnit {
        try {
            onEvent(event)
        } catch (throwable: Throwable) {
            LOGGER.debug("Failed to emit a tracing span for baker event {}", event, throwable)
        }
        return BoxedUnit.UNIT
    }

    private fun onEvent(event: BakerEvent) {
        when (event) {
            is RecipeInstanceCreated -> {
                val span = newSpan(
                    RECIPE_INSTANCE_CREATED_SPAN,
                    event.recipeId(),
                    event.recipeName(),
                    event.recipeInstanceId()
                )
                span.setStatus(StatusCode.OK)
                span.end()
            }
            is EventReceived -> {
                val span = newSpan(
                    EVENT_RECEIVED_SPAN,
                    event.recipeId(),
                    event.recipeName(),
                    event.recipeInstanceId()
                )
                span.setAttribute(BakerTraceAttributes.EVENT_NAME, event.eventName())
                val correlationId = event.correlationId()
                if (correlationId.isDefined) {
                    span.setAttribute(BakerTraceAttributes.CORRELATION_ID, correlationId.get())
                }
                span.setStatus(StatusCode.OK)
                record(event.recipeInstanceId(), span)
                span.end()
            }
            is EventFired -> {
                val span = newSpan(
                    EVENT_FIRED_SPAN,
                    event.recipeId(),
                    event.recipeName(),
                    event.recipeInstanceId()
                )
                span.setAttribute(BakerTraceAttributes.EVENT_NAME, event.eventName())
                span.setStatus(StatusCode.OK)
                record(event.recipeInstanceId(), span)
                span.end()

                if (RECIPE_SUCCESSFUL_EVENT == event.eventName()) {
                    traceContexts.remove(event.recipeInstanceId())
                    TracingMdcRegistry.remove(event.recipeInstanceId())
                }
            }
        }
    }

    private fun newSpan(name: String, recipeId: String, recipeName: String, recipeInstanceId: String): Span {
        val builder = tracer.spanBuilder(name)
            .setParent(traceContexts.parentOf(recipeInstanceId))
        val span = builder.startSpan()
        span.setAttribute(BakerTraceAttributes.RECIPE_ID, recipeId)
        span.setAttribute(BakerTraceAttributes.RECIPE_NAME, recipeName)
        span.setAttribute(BakerTraceAttributes.RECIPE_INSTANCE_ID, recipeInstanceId)
        return span
    }

    private fun record(recipeInstanceId: String, span: Span) {
        TracingMdcRegistry.put(
            recipeInstanceId,
            span.spanContext.traceId,
            span.spanContext.spanId
        )
        traceContexts.putIfAbsent(recipeInstanceId, Context.current().with(span))
    }

    companion object {
        private val LOGGER: Logger = LoggerFactory.getLogger(BakerEventTracingListener::class.java)

        private const val RECIPE_INSTANCE_CREATED_SPAN = "baker.recipe-instance.created"
        private const val EVENT_RECEIVED_SPAN = "baker.event.received"
        private const val EVENT_FIRED_SPAN = "baker.event.fired"
        private const val RECIPE_SUCCESSFUL_EVENT = "RecipeSuccessful"
    }
}
