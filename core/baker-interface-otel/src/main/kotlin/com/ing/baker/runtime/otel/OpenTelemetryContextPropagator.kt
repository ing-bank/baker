package com.ing.baker.runtime.otel

import com.ing.baker.runtime.model.propagation.ContextScope
import com.ing.baker.runtime.model.propagation.ContextSnapshot
import com.ing.baker.runtime.model.propagation.ExecutionContextPropagator
import io.opentelemetry.context.Context
import io.opentelemetry.context.ContextStorage
import io.opentelemetry.context.Scope

/**
 * Moves the OpenTelemetry [Context] of the submitting thread to the thread that actually executes the
 * work, and removes it again afterwards.
 *
 * Registered through `META-INF/services`, so simply having this module on the classpath makes
 * Baker's internal thread hops context aware.
 */
class OpenTelemetryContextPropagator : ExecutionContextPropagator {

    override fun capture(): ContextSnapshot {
        val captured = Context.current()
        return object : ContextSnapshot {
            override fun restore(): ContextScope {
                val scope = captured.makeCurrent()
                return ContextScope { scope.close() }
            }
        }
    }

    override fun clear() {
        ContextStorage.get().attach(Context.root())
    }
}
