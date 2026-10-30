package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.model.propagation.ContextScope;
import com.ing.baker.runtime.model.propagation.ContextSnapshot;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.ContextStorage;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor;
import org.junit.jupiter.api.Test;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class OpenTelemetryContextPropagatorTest {

    private static final String INVALID_TRACE_ID = "00000000000000000000000000000000";

    private final OpenTelemetryContextPropagator propagator = new OpenTelemetryContextPropagator();

    @Test
    void movesTheCapturedContextToTheExecutingThread() throws Exception {
        try (TracerFixture fixture = TracerFixture.create()) {
            final Span span = fixture.tracer().spanBuilder("caller").startSpan();
            final ContextSnapshot snapshot;
            try (io.opentelemetry.context.Scope ignored = span.makeCurrent()) {
                snapshot = propagator.capture();
            }

            final ExecutorService executor = Executors.newSingleThreadExecutor();
            try {
                final Future<String> observed = executor.submit(() -> {
                    try (ContextScope scope = snapshot.restore()) {
                        return Span.current().getSpanContext().getSpanId();
                    }
                });
                assertEquals(span.getSpanContext().getSpanId(), observed.get(5, TimeUnit.SECONDS));

                final Future<String> afterScope = executor.submit(
                        () -> Span.current().getSpanContext().getTraceId());
                assertEquals(INVALID_TRACE_ID, afterScope.get(5, TimeUnit.SECONDS),
                        "The propagated context must not survive the scope it was restored in");
            } finally {
                executor.shutdownNow();
            }
            span.end();
        }
    }

    @Test
    void clearsContextLeakedByPreviousWorkOnTheSameThread() throws Exception {
        try (TracerFixture fixture = TracerFixture.create()) {
            final ExecutorService executor = Executors.newSingleThreadExecutor();
            try {
                final Span leaked = fixture.tracer().spanBuilder("leaked").startSpan();
                executor.submit(() -> ContextStorage.get().attach(Context.current().with(leaked)))
                        .get(5, TimeUnit.SECONDS);

                final Future<String> stillLeaking = executor.submit(
                        () -> Span.current().getSpanContext().getSpanId());
                assertEquals(leaked.getSpanContext().getSpanId(), stillLeaking.get(5, TimeUnit.SECONDS));

                final Future<String> afterClear = executor.submit(() -> {
                    propagator.clear();
                    return Span.current().getSpanContext().getTraceId();
                });
                assertEquals(INVALID_TRACE_ID, afterClear.get(5, TimeUnit.SECONDS));
                assertNotEquals(INVALID_TRACE_ID, leaked.getSpanContext().getTraceId());
                assertFalse(Span.current().getSpanContext().isValid(),
                        "The test thread itself should not have any ambient span");
                leaked.end();
            } finally {
                executor.shutdownNow();
            }
        }
    }

    record TracerFixture(InMemorySpanExporter exporter, SdkTracerProvider tracerProvider,
                         io.opentelemetry.api.trace.Tracer tracer) implements AutoCloseable {

        static TracerFixture create() {
            final InMemorySpanExporter exporter = InMemorySpanExporter.create();
            final SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
                    .addSpanProcessor(SimpleSpanProcessor.create(exporter))
                    .build();
            final OpenTelemetrySdk sdk = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build();
            return new TracerFixture(exporter, tracerProvider, sdk.getTracer("test.otel.propagator"));
        }

        @Override
        public void close() {
            tracerProvider.close();
            exporter.reset();
        }
    }
}
