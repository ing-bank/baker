package com.ing.baker.runtime.otel

import com.ing.baker.runtime.model.InteractionCallContext
import com.ing.baker.runtime.model.InteractionInstrumentation
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.context.Context
import io.opentelemetry.context.Scope
import org.slf4j.MDC
import java.util.concurrent.CompletionException
import java.util.concurrent.CompletionStage
import java.util.concurrent.ExecutionException
import java.util.function.Supplier

/**
 * Starts a span for every interaction invocation and attaches it to the thread that runs the interaction, so
 * `Span.current()` inside an interaction always belongs to that very invocation, even when
 * interactions of different recipe instances share a thread pool.
 */
class OpenTelemetryInteractionInstrumentation(
    private val tracer: Tracer,
    private val parentContexts: RecipeInstanceTraceContexts
) : InteractionInstrumentation {

    override fun <A> aroundInteraction(context: InteractionCallContext, interaction: Supplier<A>): A {
        val span = try {
            startSpan(context)
        } catch (throwable: Throwable) {
            return interaction.get()
        }

        val previousTraceId = MDC.get(TRACE_ID_MDC_KEY)
        val previousSpanId = MDC.get(SPAN_ID_MDC_KEY)
        var endsAsynchronously = false

        return try {
            span.makeCurrent().use {
                MDC.put(TRACE_ID_MDC_KEY, span.spanContext.traceId)
                MDC.put(SPAN_ID_MDC_KEY, span.spanContext.spanId)

                val result = interaction.get()
                if (result is CompletionStage<*>) {
                    endsAsynchronously = true
                    result.whenComplete { _, throwable -> end(span, throwable) }
                } else {
                    span.setStatus(StatusCode.OK)
                }
                result
            }
        } catch (throwable: Throwable) {
            endsAsynchronously = false
            recordFailure(span, throwable)
            throw throwable
        } finally {
            restore(TRACE_ID_MDC_KEY, previousTraceId)
            restore(SPAN_ID_MDC_KEY, previousSpanId)
            if (!endsAsynchronously) {
                span.end()
            }
        }
    }

    private fun startSpan(context: InteractionCallContext): Span {
        val parent = parentContexts.parentOf(context.recipeInstanceId)
        val span = tracer.spanBuilder("baker.interaction." + context.interactionName)
            .setParent(parent)
            .startSpan()
        span.setAttribute(BakerTraceAttributes.RECIPE_ID, context.recipeId)
        span.setAttribute(BakerTraceAttributes.RECIPE_NAME, context.recipeName)
        span.setAttribute(BakerTraceAttributes.RECIPE_INSTANCE_ID, context.recipeInstanceId)
        span.setAttribute(BakerTraceAttributes.INTERACTION_NAME, context.interactionName)
        context.correlationId
            .ifPresent { correlationId -> span.setAttribute(BakerTraceAttributes.CORRELATION_ID, correlationId) }
        return span
    }

    companion object {
        private const val TRACE_ID_MDC_KEY = "trace_id"
        private const val SPAN_ID_MDC_KEY = "span_id"

        private fun end(span: Span, throwable: Throwable?) {
            if (throwable == null) {
                span.setStatus(StatusCode.OK)
            } else {
                recordFailure(span, throwable)
            }
            span.end()
        }

        private fun recordFailure(span: Span, throwable: Throwable) {
            val cause = unwrap(throwable)
            span.setAttribute(BakerTraceAttributes.ERROR_TYPE, BakerTraceAttributes.INTERACTION_FAILURE)
            span.recordException(cause)
            span.setStatus(
                StatusCode.ERROR,
                cause.message ?: cause.toString()
            )
        }

        private fun unwrap(throwable: Throwable): Throwable {
            return if ((throwable is CompletionException || throwable is ExecutionException)
                && throwable.cause != null
            ) {
                throwable.cause!!
            } else {
                throwable
            }
        }

        private fun restore(key: String, value: String?) {
            if (value == null) {
                MDC.remove(key)
            } else {
                MDC.put(key, value)
            }
        }
    }
}
