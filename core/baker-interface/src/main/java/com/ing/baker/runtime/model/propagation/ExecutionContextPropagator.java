package com.ing.baker.runtime.model.propagation;

/**
 * Propagates ambient thread state (MDC, tracing context, ...) across Baker's internal thread hops.
 *
 * <p>Implementations are discovered through {@link java.util.ServiceLoader} and must be thread safe.
 * {@link #capture()} is always called on the submitting thread, {@link ContextSnapshot#restore()} and
 * {@link ContextScope#close()} on the executing thread.
 */
public interface ExecutionContextPropagator {

    ContextSnapshot capture();

    /**
     * Drops any ambient state left behind on the calling thread, so a pooled thread never exposes
     * state of a previously executed task.
     */
    default void clear() {
    }
}
