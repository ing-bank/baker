package com.ing.baker.runtime.model;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

/**
 * Shares best-effort trace/span ids for MDC enrichment across runtime modules.
 *
 * <p>Only used for log lines emitted by Baker itself, outside of an interaction invocation. Inside an
 * interaction the exact trace context is attached to the executing thread by
 * {@link InteractionInstrumentation}. Entries are bounded so an abandoned recipe instance can never grow
 * this registry indefinitely.
 */
public final class TracingMdcRegistry {

    private static final int MAX_ENTRIES = 10_000;

    private static final Map<String, TraceContext> contexts = Collections.synchronizedMap(
            new LinkedHashMap<String, TraceContext>(256, 0.75f, false) {
                @Override
                protected boolean removeEldestEntry(Map.Entry<String, TraceContext> eldest) {
                    return size() > MAX_ENTRIES;
                }
            });

    private TracingMdcRegistry() {
    }

    public static void put(String recipeInstanceId, String traceId, String spanId) {
        if (recipeInstanceId == null || traceId == null || spanId == null) {
            return;
        }
        contexts.put(recipeInstanceId, new TraceContext(traceId, spanId));
    }

    public static Optional<TraceContext> get(String recipeInstanceId) {
        return Optional.ofNullable(contexts.get(recipeInstanceId));
    }

    public static void remove(String recipeInstanceId) {
        if (recipeInstanceId == null) {
            return;
        }
        contexts.remove(recipeInstanceId);
    }

    public static final class TraceContext {
        private final String traceId;
        private final String spanId;

        public TraceContext(String traceId, String spanId) {
            this.traceId = traceId;
            this.spanId = spanId;
        }

        public String getTraceId() {
            return traceId;
        }

        public String getSpanId() {
            return spanId;
        }
    }
}

