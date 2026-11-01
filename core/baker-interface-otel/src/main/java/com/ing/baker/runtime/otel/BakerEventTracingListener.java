package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.model.TracingMdcRegistry;
import com.ing.baker.runtime.scaladsl.BakerEvent;
import com.ing.baker.runtime.scaladsl.EventFired;
import com.ing.baker.runtime.scaladsl.EventReceived;
import com.ing.baker.runtime.scaladsl.RecipeInstanceCreated;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanBuilder;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Option;
import scala.runtime.AbstractFunction1;
import scala.runtime.BoxedUnit;

/**
 * Emits OpenTelemetry spans for the lifecycle and event {@link BakerEvent}s of a Baker runtime.
 *
 * <p>Besides emitting spans this listener maintains the per recipe instance trace context that interaction spans
 * are parented to, so it must share its {@link RecipeInstanceTraceContexts} instance with the
 * {@link OpenTelemetryInteractionInstrumentation} of the same Baker.
 *
 * <p>It is a {@code scala.Function1<BakerEvent, BoxedUnit>} so it can be handed directly to
 * {@code Baker.registerBakerEventListener}.
 */
public final class BakerEventTracingListener extends AbstractFunction1<BakerEvent, BoxedUnit> {

    private static final Logger LOGGER = LoggerFactory.getLogger(BakerEventTracingListener.class);

    private static final String RECIPE_INSTANCE_CREATED_SPAN = "baker.recipe-instance.created";
    private static final String EVENT_RECEIVED_SPAN = "baker.event.received";
    private static final String EVENT_FIRED_SPAN = "baker.event.fired";
    private static final String RECIPE_SUCCESSFUL_EVENT = "RecipeSuccessful";

    private final Tracer tracer;
    private final RecipeInstanceTraceContexts traceContexts;

    public BakerEventTracingListener(Tracer tracer, RecipeInstanceTraceContexts traceContexts) {
        this.tracer = tracer;
        this.traceContexts = traceContexts;
    }

    @Override
    public BoxedUnit apply(BakerEvent event) {
        try {
            onEvent(event);
        } catch (Throwable throwable) {
            // Tracing must never break the event stream.
            LOGGER.debug("Failed to emit a tracing span for baker event {}", event, throwable);
        }
        return BoxedUnit.UNIT;
    }

    private void onEvent(BakerEvent event) {
        if (event instanceof RecipeInstanceCreated) {
            final RecipeInstanceCreated created = (RecipeInstanceCreated) event;
            final Span span = newSpan(RECIPE_INSTANCE_CREATED_SPAN,
                    created.recipeId(), created.recipeName(), created.recipeInstanceId());
            span.setStatus(StatusCode.OK);
            span.end();
        } else if (event instanceof EventReceived) {
            final EventReceived received = (EventReceived) event;
            final Span span = newSpan(EVENT_RECEIVED_SPAN,
                    received.recipeId(), received.recipeName(), received.recipeInstanceId());
            span.setAttribute(BakerTraceAttributes.EVENT_NAME, received.eventName());
            final Option<String> correlationId = received.correlationId();
            if (correlationId.isDefined()) {
                span.setAttribute(BakerTraceAttributes.CORRELATION_ID, correlationId.get());
            }
            span.setStatus(StatusCode.OK);
            record(received.recipeInstanceId(), span);
            span.end();
        } else if (event instanceof EventFired) {
            final EventFired fired = (EventFired) event;
            final Span span = newSpan(EVENT_FIRED_SPAN,
                    fired.recipeId(), fired.recipeName(), fired.recipeInstanceId());
            span.setAttribute(BakerTraceAttributes.EVENT_NAME, fired.eventName());
            span.setStatus(StatusCode.OK);
            record(fired.recipeInstanceId(), span);
            span.end();

            if (RECIPE_SUCCESSFUL_EVENT.equals(fired.eventName())) {
                traceContexts.remove(fired.recipeInstanceId());
                TracingMdcRegistry.remove(fired.recipeInstanceId());
            }
        }
    }

    private Span newSpan(String name, String recipeId, String recipeName, String recipeInstanceId) {
        final SpanBuilder builder = tracer.spanBuilder(name);
        final Span span = builder.startSpan();
        span.setAttribute(BakerTraceAttributes.RECIPE_ID, recipeId);
        span.setAttribute(BakerTraceAttributes.RECIPE_NAME, recipeName);
        span.setAttribute(BakerTraceAttributes.RECIPE_INSTANCE_ID, recipeInstanceId);
        return span;
    }

    private void record(String recipeInstanceId, Span span) {
        TracingMdcRegistry.put(recipeInstanceId, span.getSpanContext().getTraceId(), span.getSpanContext().getSpanId());
        traceContexts.put(recipeInstanceId, Context.current().with(span));
    }
}
