package com.ing.baker.runtime.model.propagation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.ServiceLoader;
import java.util.concurrent.CopyOnWriteArrayList;

/**
 * Registry of the {@link ExecutionContextPropagator}s used whenever Baker hands work to another thread.
 *
 * <p>Besides the built-in {@link MdcContextPropagator}, implementations are discovered through
 * {@link ServiceLoader}, so runtimes such as {@code baker-interface-otel} can plug in without adding
 * dependencies to {@code baker-interface}.
 */
public final class ExecutionContextPropagators {

    private static final Logger logger = LoggerFactory.getLogger(ExecutionContextPropagators.class);

    private static final List<ExecutionContextPropagator> propagators = new CopyOnWriteArrayList<>();

    static {
        reload();
    }

    private ExecutionContextPropagators() {
    }

    /**
     * Captures the ambient context of the calling thread.
     */
    public static ContextSnapshot capture() {
        if (propagators.isEmpty()) {
            return ContextSnapshot.NOOP;
        }
        final List<ContextSnapshot> snapshots = new ArrayList<>(propagators.size());
        for (ExecutionContextPropagator propagator : propagators) {
            try {
                final ContextSnapshot snapshot = propagator.capture();
                if (snapshot != null) {
                    snapshots.add(snapshot);
                }
            } catch (Throwable throwable) {
                logger.debug("Context propagator {} failed to capture context", propagator, throwable);
            }
        }
        if (snapshots.isEmpty()) {
            return ContextSnapshot.NOOP;
        }
        return () -> restoreAll(snapshots);
    }

    /**
     * Drops ambient context left behind on the calling thread by previously executed work.
     */
    public static void clear() {
        for (ExecutionContextPropagator propagator : propagators) {
            try {
                propagator.clear();
            } catch (Throwable throwable) {
                logger.debug("Context propagator {} failed to clear context", propagator, throwable);
            }
        }
    }

    public static void register(ExecutionContextPropagator propagator) {
        if (propagator != null) {
            propagators.add(propagator);
        }
    }

    public static void unregister(ExecutionContextPropagator propagator) {
        propagators.remove(propagator);
    }

    public static List<ExecutionContextPropagator> registered() {
        return Collections.unmodifiableList(new ArrayList<>(propagators));
    }

    /**
     * Rebuilds the registry from the built-in propagators and the ones found on the classpath.
     */
    public static void reload() {
        final List<ExecutionContextPropagator> discovered = new ArrayList<>();
        discovered.add(new MdcContextPropagator());
        try {
            for (ExecutionContextPropagator propagator : ServiceLoader.load(
                    ExecutionContextPropagator.class, ExecutionContextPropagators.class.getClassLoader())) {
                discovered.add(propagator);
            }
        } catch (Throwable throwable) {
            logger.warn("Failed to load context propagators, continuing without them", throwable);
        }
        propagators.clear();
        propagators.addAll(discovered);
    }

    private static ContextScope restoreAll(List<ContextSnapshot> snapshots) {
        final List<ContextScope> scopes = new ArrayList<>(snapshots.size());
        for (ContextSnapshot snapshot : snapshots) {
            try {
                final ContextScope scope = snapshot.restore();
                if (scope != null) {
                    scopes.add(scope);
                }
            } catch (Throwable throwable) {
                logger.debug("Failed to restore propagated context", throwable);
            }
        }
        return () -> {
            for (int index = scopes.size() - 1; index >= 0; index--) {
                try {
                    scopes.get(index).close();
                } catch (Throwable throwable) {
                    logger.debug("Failed to close propagated context scope", throwable);
                }
            }
        };
    }
}
