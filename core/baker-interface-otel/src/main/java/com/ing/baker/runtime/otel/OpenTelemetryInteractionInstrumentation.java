package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.model.InteractionCallContext;
import com.ing.baker.runtime.model.InteractionInstrumentation;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.Scope;
import org.slf4j.MDC;

import java.util.concurrent.CompletionException;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.ExecutionException;
import java.util.function.Supplier;

/**
 * Starts a span for every interaction invocation and attaches it to the thread that runs the interaction, so
 * {@code Span.current()} inside an interaction always belongs to that very invocation, even when
 * interactions of different recipe instances share a thread pool.
 */
public final class OpenTelemetryInteractionInstrumentation implements InteractionInstrumentation {

    private static final String TRACE_ID_MDC_KEY = "trace_id";
    private static final String SPAN_ID_MDC_KEY = "span_id";

    private final Tracer tracer;
    private final RecipeInstanceTraceContexts parentContexts;

    public OpenTelemetryInteractionInstrumentation(Tracer tracer, RecipeInstanceTraceContexts parentContexts) {
        this.tracer = tracer;
        this.parentContexts = parentContexts;
    }

    @Override
    public <A> A aroundInteraction(InteractionCallContext context, Supplier<A> interaction) {
        final Span span;
        try {
            span = startSpan(context);
        } catch (Throwable throwable) {
            // Tracing must never break execution.
            return interaction.get();
        }

        final String previousTraceId = MDC.get(TRACE_ID_MDC_KEY);
        final String previousSpanId = MDC.get(SPAN_ID_MDC_KEY);
        boolean endsAsynchronously = false;

        try (Scope ignored = span.makeCurrent()) {
            MDC.put(TRACE_ID_MDC_KEY, span.getSpanContext().getTraceId());
            MDC.put(SPAN_ID_MDC_KEY, span.getSpanContext().getSpanId());

            final A result = interaction.get();
            if (result instanceof CompletionStage) {
                endsAsynchronously = true;
                ((CompletionStage<?>) result).whenComplete((value, throwable) -> end(span, throwable));
            } else {
                span.setStatus(StatusCode.OK);
            }
            return result;
        } catch (Throwable throwable) {
            endsAsynchronously = false;
            recordFailure(span, throwable);
            throw throwable;
        } finally {
            restore(TRACE_ID_MDC_KEY, previousTraceId);
            restore(SPAN_ID_MDC_KEY, previousSpanId);
            if (!endsAsynchronously) {
                span.end();
            }
        }
    }

    private Span startSpan(InteractionCallContext context) {
        final Context parent = parentContexts.parentOf(context.getRecipeInstanceId());
        final Span span = tracer.spanBuilder("baker.interaction." + context.getInteractionName())
                .setParent(parent)
                .startSpan();
        span.setAttribute(BakerTraceAttributes.RECIPE_ID, context.getRecipeId());
        span.setAttribute(BakerTraceAttributes.RECIPE_NAME, context.getRecipeName());
        span.setAttribute(BakerTraceAttributes.RECIPE_INSTANCE_ID, context.getRecipeInstanceId());
        span.setAttribute(BakerTraceAttributes.INTERACTION_NAME, context.getInteractionName());
        context.getCorrelationId()
                .ifPresent(correlationId -> span.setAttribute(BakerTraceAttributes.CORRELATION_ID, correlationId));
        return span;
    }

    private static void end(Span span, Throwable throwable) {
        if (throwable == null) {
            span.setStatus(StatusCode.OK);
        } else {
            recordFailure(span, throwable);
        }
        span.end();
    }

    private static void recordFailure(Span span, Throwable throwable) {
        final Throwable cause = unwrap(throwable);
        span.setAttribute(BakerTraceAttributes.ERROR_TYPE, BakerTraceAttributes.INTERACTION_FAILURE);
        span.recordException(cause);
        span.setStatus(StatusCode.ERROR, cause.getMessage() == null ? cause.toString() : cause.getMessage());
    }

    private static Throwable unwrap(Throwable throwable) {
        if ((throwable instanceof CompletionException || throwable instanceof ExecutionException)
                && throwable.getCause() != null) {
            return throwable.getCause();
        }
        return throwable;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            MDC.remove(key);
        } else {
            MDC.put(key, value);
        }
    }
}
