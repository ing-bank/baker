package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.catseffect.SyncSupport;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.ContextStorage;
import io.opentelemetry.context.Scope;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.testing.exporter.InMemorySpanExporter;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.SimpleSpanProcessor;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.MDC;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Verifies that the propagator registered through {@code META-INF/services} is picked up by Baker's blocking
 * pool, which is where interaction implementations run.
 */
class BlockingPoolPropagationTest {

    private static final String INVALID_TRACE_ID = "00000000000000000000000000000000";

    private InMemorySpanExporter exporter;
    private SdkTracerProvider tracerProvider;
    private io.opentelemetry.api.trace.Tracer tracer;

    @BeforeEach
    void setUp() {
        exporter = InMemorySpanExporter.create();
        tracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(SimpleSpanProcessor.create(exporter))
                .build();
        tracer = OpenTelemetrySdk.builder().setTracerProvider(tracerProvider).build().getTracer("test.otel.blocking");
    }

    @AfterEach
    void tearDown() {
        tracerProvider.close();
        exporter.reset();
        MDC.clear();
    }

    private static <A> A runBlocking(scala.Function0<A> thunk) throws Exception {
        final CompletableFuture<A> future =
                SyncSupport.fromCompletableFuture().blocking(thunk);
        return future.get(10, TimeUnit.SECONDS);
    }

    @Test
    void propagatesSpanAndMdcToTheBlockingPool() throws Exception {
        final Span span = tracer.spanBuilder("caller").startSpan();
        MDC.put("recipeInstanceId", "instance-1");
        try (Scope ignored = span.makeCurrent()) {
            final String[] observed = runBlocking(() -> new String[]{
                    Span.current().getSpanContext().getSpanId(),
                    MDC.get("recipeInstanceId")
            });
            assertEquals(span.getSpanContext().getSpanId(), observed[0]);
            assertEquals("instance-1", observed[1]);
        } finally {
            span.end();
            MDC.clear();
        }
    }

    @Test
    void doesNotExposeContextOfPreviousWorkOnTheSamePooledThread() throws Exception {
        final Span leaked = tracer.spanBuilder("leaked").startSpan();

        // Simulate badly behaved work that attaches a context on the pooled thread without detaching it.
        runBlocking(() -> {
            ContextStorage.get().attach(Context.current().with(leaked));
            MDC.put("trace_id", "leaked-trace");
            return null;
        });

        final String[] observed = runBlocking(() -> new String[]{
                Span.current().getSpanContext().getTraceId(),
                MDC.get("trace_id")
        });

        assertEquals(INVALID_TRACE_ID, observed[0], "A pooled thread must not expose the context of previous work");
        assertEquals(null, observed[1], "A pooled thread must not expose the MDC of previous work");
        leaked.end();
    }
}
