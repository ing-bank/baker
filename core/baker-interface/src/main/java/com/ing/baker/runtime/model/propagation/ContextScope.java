package com.ing.baker.runtime.model.propagation;

/**
 * Undoes a {@link ContextSnapshot#restore()} on the thread that performed it.
 */
@FunctionalInterface
public interface ContextScope extends AutoCloseable {

    ContextScope NOOP = () -> {
    };

    @Override
    void close();
}
