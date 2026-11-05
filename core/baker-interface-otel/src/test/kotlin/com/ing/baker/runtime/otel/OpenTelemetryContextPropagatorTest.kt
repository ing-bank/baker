package com.ing.baker.runtime.otel

import com.ing.baker.runtime.model.propagation.ContextScope
import com.ing.baker.runtime.model.propagation.ContextSnapshot
import io.opentelemetry.api.trace.Span
import io.opentelemetry.context.Context
import io.opentelemetry.context.ContextStorage
import io.opentelemetry.sdk.OpenTelemetrySdk
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter
import io.opentelemetry.sdk.trace.SdkTracerProvider
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Test
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit

class OpenTelemetryContextPropagatorTest {

    private val propagator = OpenTelemetryContextPropagator()

    @Test
    fun movesTheCapturedContextToTheExecutingThread() {
        TracerFixture.create().use { fixture ->
            val span = fixture.tracer.spanBuilder("caller").startSpan()
            val snapshot: ContextSnapshot = span.makeCurrent().use {
                propagator.capture()
            }

            val executor = Executors.newSingleThreadExecutor()
            try {
                val observed = executor.submit<String> {
                    snapshot.restore().use { _: ContextScope ->
                        Span.current().spanContext.spanId
                    }
                }
                assertEquals(span.spanContext.spanId, observed.get(5, TimeUnit.SECONDS))

                val afterScope = executor.submit<String> {
                    Span.current().spanContext.traceId
                }
                assertEquals(
                    INVALID_TRACE_ID,
                    afterScope.get(5, TimeUnit.SECONDS),
                    "The propagated context must not survive the scope it was restored in"
                )
            } finally {
                executor.shutdownNow()
            }
            span.end()
        }
    }

    @Test
    fun clearsContextLeakedByPreviousWorkOnTheSameThread() {
        TracerFixture.create().use { fixture ->
            val executor = Executors.newSingleThreadExecutor()
            try {
                val leaked = fixture.tracer.spanBuilder("leaked").startSpan()
                executor.submit {
                    ContextStorage.get().attach(Context.current().with(leaked))
                }.get(5, TimeUnit.SECONDS)

                val stillLeaking = executor.submit<String> {
                    Span.current().spanContext.spanId
                }
                assertEquals(leaked.spanContext.spanId, stillLeaking.get(5, TimeUnit.SECONDS))

                val afterClear = executor.submit<String> {
                    propagator.clear()
                    Span.current().spanContext.traceId
                }
                assertEquals(INVALID_TRACE_ID, afterClear.get(5, TimeUnit.SECONDS))
                assertNotEquals(INVALID_TRACE_ID, leaked.spanContext.traceId)
                assertFalse(
                    Span.current().spanContext.isValid,
                    "The test thread itself should not have any ambient span"
                )
                leaked.end()
            } finally {
                executor.shutdownNow()
            }
        }
    }

    private data class TracerFixture(
        val exporter: InMemorySpanExporter,
        val tracerProvider: SdkTracerProvider,
        val tracer: io.opentelemetry.api.trace.Tracer
    ) : AutoCloseable {

        companion object {
            fun create(): TracerFixture {
                val exporter = InMemorySpanExporter.create()
                val tracerProvider = SdkTracerProvider.builder()
                    .addSpanProcessor(SimpleSpanProcessor.create(exporter))
                    .build()
                val sdk = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build()
                return TracerFixture(exporter, tracerProvider, sdk.getTracer("test.otel.propagator"))
            }
        }

        override fun close() {
            tracerProvider.close()
            exporter.reset()
        }
    }

    companion object {
        private const val INVALID_TRACE_ID = "00000000000000000000000000000000"
    }
}
