package com.ing.baker.runtime.otel;

import com.ing.baker.runtime.model.propagation.ContextScope;
import com.ing.baker.runtime.model.propagation.ContextSnapshot;
import com.ing.baker.runtime.model.propagation.ExecutionContextPropagator;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.ContextStorage;
import io.opentelemetry.context.Scope;

/**
 * Moves the OpenTelemetry {@link Context} of the submitting thread to the thread that actually executes the
 * work, and removes it again afterwards.
 *
 * <p>Registered through {@code META-INF/services}, so simply having this module on the classpath makes
 * Baker's internal thread hops context aware.
 */
public final class OpenTelemetryContextPropagator implements ExecutionContextPropagator {

    @Override
    public ContextSnapshot capture() {
        final Context captured = Context.current();
        return () -> {
            final Scope scope = captured.makeCurrent();
            return (ContextScope) scope::close;
        };
    }

    @Override
    public void clear() {
        // Detaches whatever context a previous task left attached to this (pooled) thread. The returned scope
        // is intentionally not closed: closing it would restore exactly the leaked context we want gone.
        ContextStorage.get().attach(Context.root());
    }
}
