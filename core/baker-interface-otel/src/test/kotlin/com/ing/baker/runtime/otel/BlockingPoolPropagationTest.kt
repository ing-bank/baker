package com.ing.baker.runtime.otel

import com.ing.baker.runtime.catseffect.SyncSupport
import io.opentelemetry.api.trace.Span
import io.opentelemetry.context.Context
import io.opentelemetry.context.ContextStorage
import io.opentelemetry.context.Scope
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.slf4j.MDC
import java.util.concurrent.CompletableFuture
import java.util.concurrent.TimeUnit

/**
 * Verifies that the propagator registered through {@code META-INF/services} is picked up by Baker's blocking
 * pool, which is where interaction implementations run.
 */
class BlockingPoolPropagationTest {

    private lateinit var exporter: InMemorySpanExporter
    private lateinit var tracerProvider: SdkTracerProvider
    private lateinit var tracer: io.opentelemetry.api.trace.Tracer

    @BeforeEach
    fun setUp() {
        exporter = InMemorySpanExporter.create()
        tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(SimpleSpanProcessor.create(exporter))
            .build()
        tracer = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build().getTracer("test.otel.blocking")
    }

    @AfterEach
    fun tearDown() {
        tracerProvider.close()
        exporter.reset()
        MDC.clear()
    }

    @Test
    fun propagatesSpanAndMdcToTheBlockingPool() {
        val span = tracer.spanBuilder("caller").startSpan()
        MDC.put("recipeInstanceId", "instance-1")
        try {
            span.makeCurrent().use {
                val observed = runBlocking {
                    arrayOf(
                        Span.current().spanContext.spanId,
                        MDC.get("recipeInstanceId")
                    )
                }
                assertEquals(span.spanContext.spanId, observed[0])
                assertEquals("instance-1", observed[1])
            }
        } finally {
            span.end()
            MDC.clear()
        }
    }

    @Test
    fun doesNotExposeContextOfPreviousWorkOnTheSamePooledThread() {
        val leaked = tracer.spanBuilder("leaked").startSpan()

        // Simulate badly behaved work that attaches a context on the pooled thread without detaching it.
        runBlocking {
            ContextStorage.get().attach(Context.current().with(leaked))
            MDC.put("trace_id", "leaked-trace")
            null
        }

        val observed = runBlocking {
            arrayOf(
                Span.current().spanContext.traceId,
                MDC.get("trace_id")
            )
        }

        assertEquals(INVALID_TRACE_ID, observed[0], "A pooled thread must not expose the context of previous work")
        assertNull(observed[1], "A pooled thread must not expose the MDC of previous work")
        leaked.end()
    }

    private fun <A> runBlocking(thunk: () -> A): A {
        @Suppress("UNCHECKED_CAST")
        val future = SyncSupport.fromCompletableFuture().blocking(
            object : scala.Function0<A> {
                override fun apply(): A = thunk()
            }
        ) as CompletableFuture<A>
        return future.get(10, TimeUnit.SECONDS)
    }

    companion object {
        private const val INVALID_TRACE_ID = "00000000000000000000000000000000"
    }
}
