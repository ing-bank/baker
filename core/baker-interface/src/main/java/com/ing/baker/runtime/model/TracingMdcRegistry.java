package com.ing.baker.runtime.model;

import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Shares best-effort trace/span ids for MDC enrichment across runtime modules.
 */
public final class TracingMdcRegistry {

    private static final ConcurrentHashMap<String, TraceContext> contexts = new ConcurrentHashMap<>();

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

