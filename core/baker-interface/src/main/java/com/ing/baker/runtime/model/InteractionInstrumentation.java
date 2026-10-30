package com.ing.baker.runtime.model;

import java.util.function.Supplier;

/**
 * Hook invoked around every interaction invocation, on the thread that runs the interaction.
 *
 * <p>This is the extension point used for tracing: an implementation can start a span, attach it to the
 * executing thread and detach it again once the invocation returns, guaranteeing that
 * {@code Span.current()} inside an interaction belongs to that interaction only.
 */
public interface InteractionInstrumentation {

    InteractionInstrumentation NOOP = new InteractionInstrumentation() {
        @Override
        public <A> A aroundInteraction(InteractionCallContext context, Supplier<A> interaction) {
            return interaction.get();
        }
    };

    static InteractionInstrumentation noop() {
        return NOOP;
    }

    <A> A aroundInteraction(InteractionCallContext context, Supplier<A> interaction);
}
