package com.ing.baker.runtime.otel

import com.ing.baker.runtime.model.InteractionCallContext
import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.trace.Span
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import io.opentelemetry.context.Context
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.data.SpanData
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.slf4j.MDC
import java.util.concurrent.CompletableFuture

class OpenTelemetryInteractionInstrumentationTest {

    private lateinit var exporter: InMemorySpanExporter
    private lateinit var tracerProvider: SdkTracerProvider
    private lateinit var tracer: Tracer
    private lateinit var parentContexts: RecipeInstanceTraceContexts
    private lateinit var instrumentation: OpenTelemetryInteractionInstrumentation

    @BeforeEach
    fun setUp() {
        exporter = InMemorySpanExporter.create()
        tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(SimpleSpanProcessor.create(exporter))
            .build()
        tracer = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build().getTracer("test.otel")
        parentContexts = RecipeInstanceTraceContexts()
        instrumentation = OpenTelemetryInteractionInstrumentation(tracer, parentContexts)
    }

    @AfterEach
    fun tearDown() {
        tracerProvider.close()
        exporter.reset()
        MDC.clear()
    }

    @Test
    fun attachesItsOwnSpanToTheExecutingThread() {
        val observedSpanId = instrumentation.aroundInteraction(
            callContext("instance-1")
        ) { Span.current().spanContext.spanId }

        val spans: List<SpanData> = exporter.finishedSpanItems
        assertEquals(1, spans.size)
        val span = spans[0]
        assertEquals("baker.interaction.ValidateOrder", span.name)
        assertEquals(span.spanContext.spanId, observedSpanId)
        assertEquals(StatusCode.OK, span.status.statusCode)
        assertEquals("instance-1", span.attributes.get(AttributeKey.stringKey("baker.recipe.instance.id")))
        assertEquals("ValidateOrder", span.attributes.get(AttributeKey.stringKey("baker.interaction.name")))
        assertEquals("correlation-1", span.attributes.get(AttributeKey.stringKey("baker.correlation.id")))
        assertFalse(Span.current().spanContext.isValid, "The span must be detached after the invocation")
    }

    @Test
    fun parentsTheSpanToTheRecipeInstanceContext() {
        val parent = tracer.spanBuilder("baker.event.received").startSpan()
        parentContexts.put("instance-2", Context.root().with(parent))
        parent.end()

        instrumentation.aroundInteraction(callContext("instance-2")) { null }

        val interactionSpan = exporter.finishedSpanItems
            .first { it.name.startsWith("baker.interaction.") }
        assertEquals(parent.spanContext.spanId, interactionSpan.parentSpanId)
        assertEquals(parent.spanContext.traceId, interactionSpan.spanContext.traceId)
    }

    @Test
    fun setsAndRestoresTraceMdcKeys() {
        MDC.put("trace_id", "previous-trace")

        instrumentation.aroundInteraction(callContext("instance-3")) {
            assertEquals(Span.current().spanContext.traceId, MDC.get("trace_id"))
            assertEquals(Span.current().spanContext.spanId, MDC.get("span_id"))
            null
        }

        assertEquals("previous-trace", MDC.get("trace_id"))
        assertNull(MDC.get("span_id"))
    }

    @Test
    fun endsTheSpanWhenAnAsynchronousInteractionFails() {
        val future = CompletableFuture<String>()

        instrumentation.aroundInteraction(callContext("instance-4")) { future }

        assertTrue(exporter.finishedSpanItems.isEmpty(), "Span must stay open until the interaction completes")

        future.completeExceptionally(RuntimeException("Expected failure"))

        val span = exporter.finishedSpanItems[0]
        assertEquals(StatusCode.ERROR, span.status.statusCode)
        assertEquals("interaction.failure", span.attributes.get(AttributeKey.stringKey("error.type")))
    }

    @Test
    fun recordsSynchronousFailures() {
        val failure = RuntimeException("Expected failure")
        try {
            instrumentation.aroundInteraction(callContext("instance-5")) {
                throw failure
            }
        } catch (expected: RuntimeException) {
            assertEquals(failure, expected)
        }

        val span = exporter.finishedSpanItems[0]
        assertEquals(StatusCode.ERROR, span.status.statusCode)
        assertEquals("interaction.failure", span.attributes.get(AttributeKey.stringKey("error.type")))
    }

    private fun callContext(recipeInstanceId: String): InteractionCallContext =
        InteractionCallContext("recipe-id", "recipe", recipeInstanceId, "ValidateOrder", 42L, "correlation-1")
}
