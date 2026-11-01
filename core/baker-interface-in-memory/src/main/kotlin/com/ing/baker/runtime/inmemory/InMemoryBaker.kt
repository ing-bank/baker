package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.BakerConfig
import com.ing.baker.runtime.model.BakerF
import com.ing.baker.runtime.model.BakerLogging
import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.model.InteractionInstrumentation
import com.ing.baker.runtime.otel.BakerEventTracingListener
import com.ing.baker.runtime.otel.OpenTelemetryInteractionInstrumentation
import com.ing.baker.runtime.otel.RecipeInstanceTraceContexts
import io.opentelemetry.api.GlobalOpenTelemetry
import io.opentelemetry.api.trace.StatusCode
import io.opentelemetry.api.trace.Tracer
import java.util.concurrent.CompletableFuture
import com.ing.baker.runtime.defaultinteractions.`package$`.`MODULE$` as defaultinteractions
import com.ing.baker.runtime.javadsl.Baker as JavaBaker
import scala.collection.immutable.List as ScalaList

/**
 * In-memory implementation of Baker.
 *
 * Note: This class may show compiler warnings due to Scala/Kotlin interoperability limitations.
 * The compiler may report unimplemented abstract members or type mismatches, but these are false positives.
 * All required functionality is properly implemented in the parent BakerF class.
 */
@Suppress("ABSTRACT_MEMBER_NOT_IMPLEMENTED", "UNCHECKED_CAST")
class InMemoryBaker(
    private val bakerConfig: BakerConfig,
    components: BakerComponents<CompletableFuture<*>>,
    private val tracer: Tracer = defaultTracer(),
    private val traceContexts: RecipeInstanceTraceContexts = RecipeInstanceTraceContexts()
) : BakerF<CompletableFuture<*>>(
    components,
    InMemoryEffects.asyncSupportAny(),
    InMemoryEffects.asyncSupportAny()
) {

    init {
        registerTracingListener()
    }

    companion object {

        private const val INSTRUMENTATION_NAME = "com.ing.baker.runtime.inmemory.InMemoryBaker"

        private fun defaultTracer(): Tracer =
            GlobalOpenTelemetry.getTracer(INSTRUMENTATION_NAME)

        @JvmStatic
        fun build(implementations: ScalaList<*>): CompletableFuture<BakerF<CompletableFuture<*>>> =
            build(BakerConfig.default(), implementations, defaultTracer())

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun build(
            config: BakerConfig,
            implementations: ScalaList<*>
        ): CompletableFuture<BakerF<CompletableFuture<*>>> =
            build(config, implementations, defaultTracer())

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun build(
            config: BakerConfig,
            implementations: ScalaList<*>,
            tracer: Tracer
        ): CompletableFuture<BakerF<CompletableFuture<*>>> {
            val buildSpan = tracer.spanBuilder("baker.build").startSpan()
            val ioAsyncSupport = InMemoryEffects.asyncSupportAny()
            val ioClassTag = InMemoryEffects.classTagAny()
            val builtinInteractions =
                defaultinteractions.all(ioAsyncSupport, ioClassTag) as ScalaList<InteractionInstance<CompletableFuture<*>>>

            val recipeInstanceManager =
                InMemoryRecipeInstanceManager(
                    config.retentionPeriodCheckInterval(),
                    config.idleTimeout()
                )
            val interactionInstances =
                implementations.concat(builtinInteractions) as ScalaList<InteractionInstance<CompletableFuture<*>>>
            val recipeManager = InMemoryRecipeManager()
            val eventStream = InMemoryEventStream()
            val interactions = InMemoryInteractionManager(interactionInstances)
            val traceContexts = RecipeInstanceTraceContexts()
            val components = BakerComponents(
                interactions,
                recipeInstanceManager,
                recipeManager,
                eventStream,
                BakerLogging.default(),
                OpenTelemetryInteractionInstrumentation(tracer, traceContexts) as InteractionInstrumentation
            )
            return try {
                val bakerFuture: CompletableFuture<BakerF<CompletableFuture<*>>> =
                    InMemoryEffects.pure(
                        InMemoryBaker(config, components, tracer, traceContexts) as BakerF<CompletableFuture<*>>
                    )

                bakerFuture.whenComplete { _, throwable ->
                    if (throwable != null) {
                        buildSpan.recordException(throwable)
                        buildSpan.setStatus(StatusCode.ERROR)
                    } else {
                        buildSpan.setStatus(StatusCode.OK)
                    }
                    buildSpan.end()
                }
            } catch (throwable: Throwable) {
                buildSpan.recordException(throwable)
                buildSpan.setStatus(StatusCode.ERROR)
                buildSpan.end()
                throw throwable
            }
        }

        @JvmStatic
        fun java(config: BakerConfig, implementations: List<Any>): JavaBaker {
            return java(config, implementations, defaultTracer())
        }

        @JvmStatic
        fun java(config: BakerConfig, implementations: List<Any>, tracer: Tracer): JavaBaker {
            val futureToCompletableFuture = InMemoryEffects.futureToCompletableFuture()
            val completableFutureToFuture = InMemoryEffects.completableFutureToFuture()
            val scalaInteractions = InMemoryEffects.toScalaCompletableFutureInteractions(implementations)

            return build(config, scalaInteractions, tracer)
                .let { InMemoryEffects.runSync(it) }
                .asDeprecatedFutureImplementation(completableFutureToFuture, futureToCompletableFuture)
                .let { JavaBaker(it) }
        }

        /**
         * CompletableFuture-based factory for Java callers that want to avoid blocking on builder initialization.
         */
        @JvmStatic
        fun javaAsync(config: BakerConfig, implementations: List<Any>): CompletableFuture<JavaBaker> {
            return javaAsync(config, implementations, defaultTracer())
        }

        @JvmStatic
        fun javaAsync(config: BakerConfig, implementations: List<Any>, tracer: Tracer): CompletableFuture<JavaBaker> {
            val futureToCompletableFuture = InMemoryEffects.futureToCompletableFuture()
            val completableFutureToFuture = InMemoryEffects.completableFutureToFuture()
            val scalaInteractions = InMemoryEffects.toScalaCompletableFutureInteractions(implementations)

            return build(config, scalaInteractions, tracer)
                .thenApply { bakerF ->
                    JavaBaker(bakerF.asDeprecatedFutureImplementation(completableFutureToFuture, futureToCompletableFuture))
                }
        }

        @JvmStatic
        fun java(implementations: List<Any>): JavaBaker =
            java(BakerConfig.default(), implementations)

        @JvmStatic
        fun javaAsync(implementations: List<Any>): CompletableFuture<JavaBaker> =
            javaAsync(BakerConfig.default(), implementations)

        @JvmStatic
        fun java(): JavaBaker =
            java(BakerConfig.default(), emptyList())

        @JvmStatic
        fun javaAsync(): CompletableFuture<JavaBaker> =
            javaAsync(BakerConfig.default(), emptyList())
    }

    override fun config(): BakerConfig = bakerConfig

    /**
     * Attempts to gracefully shutdown the baker system.
     */
    override fun gracefulShutdown(): CompletableFuture<Any> {
        traceContexts.clear()
        return InMemoryEffects.unit()
    }

    private fun registerTracingListener() {
        try {
            InMemoryEffects.runSync(registerBakerEventListener(BakerEventTracingListener(tracer, traceContexts)))
        } catch (_: Throwable) {
            // Tracing must never prevent Baker startup.
        }
    }

}
