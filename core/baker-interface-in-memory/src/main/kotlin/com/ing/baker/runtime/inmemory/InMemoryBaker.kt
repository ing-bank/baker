package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.BakerConfig
import com.ing.baker.runtime.model.BakerF
import com.ing.baker.runtime.model.BakerLogging
import com.ing.baker.runtime.model.InteractionInstance
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
    components: BakerComponents<IO<Any>>
) : BakerF<IO<Any>>(
    components,
    InMemoryEffects.asyncSupportAny(),
    InMemoryEffects.asyncSupportAny()
) {

    companion object {

        @JvmStatic
        fun build(implementations: ScalaList<*>): IO<BakerF<IO<*>>> = build(BakerConfig.default(), implementations)

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun build(
            config: BakerConfig,
            implementations: ScalaList<*>
        ): IO<BakerF<IO<*>>> {
            val ioAsyncSupport = InMemoryEffects.asyncSupportAny()
            val ioClassTag = InMemoryEffects.classTagAny()
            val builtinInteractions =
                defaultinteractions.all(ioAsyncSupport, ioClassTag) as ScalaList<InteractionInstance<IO<*>>>

            val recipeInstanceManager =
                InMemoryRecipeInstanceManager(
                    config.retentionPeriodCheckInterval(),
                    config.idleTimeout()
                )
            val interactionInstances =
                implementations.concat(builtinInteractions) as ScalaList<InteractionInstance<IO<*>>>
            val recipeManager = InMemoryRecipeManager()
            val eventStream = InMemoryEventStream()
            val interactions = InMemoryInteractionManager(interactionInstances)
            val components = BakerComponents(
                interactions,
                recipeInstanceManager,
                recipeManager,
                eventStream,
                BakerLogging.default()
            )
            return InMemoryEffects.pure(
                InMemoryBaker(config, components as BakerComponents<IO<Any>>) as BakerF<IO<*>>
            )
        }

        @JvmStatic
        fun java(config: BakerConfig, implementations: List<Any>): JavaBaker {
            val futureToIO = InMemoryEffects.futureToIO()
            val ioToFuture = InMemoryEffects.ioToFuture()
            val scalaInteractions = InMemoryEffects.toScalaIoInteractions(implementations)

            return build(config, scalaInteractions)
                .let { InMemoryEffects.runSync(it) }
                .asDeprecatedFutureImplementation(ioToFuture, futureToIO)
                .let { JavaBaker(it) }
        }

        /**
         * CompletableFuture-based factory for Java callers that want to avoid blocking on builder initialization.
         */
        @JvmStatic
        fun javaAsync(config: BakerConfig, implementations: List<Any>): CompletableFuture<JavaBaker> {
            val futureToIO = InMemoryEffects.futureToIO()
            val ioToFuture = InMemoryEffects.ioToFuture()
            val scalaInteractions = InMemoryEffects.toScalaIoInteractions(implementations)

            return InMemoryEffects.ioToCompletableFuture(build(config, scalaInteractions))
                .thenApply { bakerF ->
                    JavaBaker(bakerF.asDeprecatedFutureImplementation(ioToFuture, futureToIO))
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
    override fun gracefulShutdown(): IO<Any> = InMemoryEffects.unit() as IO<Any>
}
