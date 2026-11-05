package com.ing.baker.runtime.model.propagation;

import org.slf4j.MDC;

import java.util.Map;

/**
 * Built-in propagator moving the SLF4J {@link MDC} across thread hops.
 */
public final class MdcContextPropagator implements ExecutionContextPropagator {

    @Override
    public ContextSnapshot capture() {
        final Map<String, String> captured = MDC.getCopyOfContextMap();
        return () -> {
            final Map<String, String> previous = MDC.getCopyOfContextMap();
            apply(captured);
            return () -> apply(previous);
        };
    }

    @Override
    public void clear() {
        MDC.clear();
    }

    private static void apply(Map<String, String> context) {
        if (context == null || context.isEmpty()) {
            MDC.clear();
        } else {
            MDC.setContextMap(context);
        }
    }
}
