package com.ing.baker.runtime.model.propagation;

/**
 * Immutable capture of ambient context taken on the submitting thread.
 */
@FunctionalInterface
public interface ContextSnapshot {

    ContextSnapshot NOOP = () -> ContextScope.NOOP;

    /**
     * Installs the captured context on the calling thread. Must be closed on that same thread.
     */
    ContextScope restore();
}
