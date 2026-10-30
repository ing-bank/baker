package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.model.InteractionCallContext;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.data.SpanData;
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.MDC;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class OpenTelemetryInteractionInstrumentationTest {

    private InMemorySpanExporter exporter;
    private SdkTracerProvider tracerProvider;
    private Tracer tracer;
    private RecipeInstanceTraceContexts parentContexts;
    private OpenTelemetryInteractionInstrumentation instrumentation;

    @BeforeEach
    void setUp() {
        exporter = InMemorySpanExporter.create();
        tracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(SimpleSpanProcessor.create(exporter))
                .build();
        tracer = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build().getTracer("test.otel");
        parentContexts = new RecipeInstanceTraceContexts();
        instrumentation = new OpenTelemetryInteractionInstrumentation(tracer, parentContexts);
    }

    @AfterEach
    void tearDown() {
        tracerProvider.close();
        exporter.reset();
        MDC.clear();
    }

    private static InteractionCallContext callContext(String recipeInstanceId) {
        return new InteractionCallContext("recipe-id", "recipe", recipeInstanceId, "ValidateOrder", 42L, "correlation-1");
    }

    @Test
    void attachesItsOwnSpanToTheExecutingThread() {
        final String observedSpanId = instrumentation.aroundInteraction(
                callContext("instance-1"),
                () -> Span.current().getSpanContext().getSpanId());

        final List<SpanData> spans = exporter.getFinishedSpanItems();
        assertEquals(1, spans.size());
        final SpanData span = spans.get(0);
        assertEquals("baker.interaction.ValidateOrder", span.getName());
        assertEquals(span.getSpanContext().getSpanId(), observedSpanId);
        assertEquals(StatusCode.OK, span.getStatus().getStatusCode());
        assertEquals("instance-1", span.getAttributes().get(AttributeKey.stringKey("baker.recipe.instance.id")));
        assertEquals("ValidateOrder", span.getAttributes().get(AttributeKey.stringKey("baker.interaction.name")));
        assertEquals("correlation-1", span.getAttributes().get(AttributeKey.stringKey("baker.correlation.id")));
        assertFalse(Span.current().getSpanContext().isValid(), "The span must be detached after the invocation");
    }

    @Test
    void parentsTheSpanToTheRecipeInstanceContext() {
        final Span parent = tracer.spanBuilder("baker.event.received").startSpan();
        parentContexts.put("instance-2", Context.root().with(parent));
        parent.end();

        instrumentation.aroundInteraction(callContext("instance-2"), () -> null);

        final SpanData interactionSpan = exporter.getFinishedSpanItems().stream()
                .filter(span -> span.getName().startsWith("baker.interaction."))
                .findFirst()
                .orElseThrow();
        assertEquals(parent.getSpanContext().getSpanId(), interactionSpan.getParentSpanId());
        assertEquals(parent.getSpanContext().getTraceId(), interactionSpan.getSpanContext().getTraceId());
    }

    @Test
    void setsAndRestoresTraceMdcKeys() {
        MDC.put("trace_id", "previous-trace");

        instrumentation.aroundInteraction(callContext("instance-3"), () -> {
            assertEquals(Span.current().getSpanContext().getTraceId(), MDC.get("trace_id"));
            assertEquals(Span.current().getSpanContext().getSpanId(), MDC.get("span_id"));
            return null;
        });

        assertEquals("previous-trace", MDC.get("trace_id"));
        assertNull(MDC.get("span_id"));
    }

    @Test
    void endsTheSpanWhenAnAsynchronousInteractionFails() {
        final CompletableFuture<String> future = new CompletableFuture<>();

        instrumentation.aroundInteraction(callContext("instance-4"), () -> future);

        assertTrue(exporter.getFinishedSpanItems().isEmpty(), "Span must stay open until the interaction completes");

        future.completeExceptionally(new RuntimeException("Expected failure"));

        final SpanData span = exporter.getFinishedSpanItems().get(0);
        assertEquals(StatusCode.ERROR, span.getStatus().getStatusCode());
        assertEquals("interaction.failure", span.getAttributes().get(AttributeKey.stringKey("error.type")));
    }

    @Test
    void recordsSynchronousFailures() {
        final RuntimeException failure = new RuntimeException("Expected failure");
        try {
            instrumentation.aroundInteraction(callContext("instance-5"), () -> {
                throw failure;
            });
        } catch (RuntimeException expected) {
            assertEquals(failure, expected);
        }

        final SpanData span = exporter.getFinishedSpanItems().get(0);
        assertEquals(StatusCode.ERROR, span.getStatus().getStatusCode());
        assertEquals("interaction.failure", span.getAttributes().get(AttributeKey.stringKey("error.type")));
    }
}
