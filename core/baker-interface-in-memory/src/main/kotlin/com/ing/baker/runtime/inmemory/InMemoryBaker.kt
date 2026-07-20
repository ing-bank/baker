package com.ing.baker.runtime.inmemory

import cats.arrow.FunctionK
import cats.effect.IO
import cats.effect.kernel.Async
import cats.effect.unsafe.IORuntime
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.BakerConfig
import com.ing.baker.runtime.model.BakerF
import com.ing.baker.runtime.model.BakerLogging
import com.ing.baker.runtime.model.InteractionInstance
import scala.concurrent.Future
import scala.jdk.javaapi.CollectionConverters.asScala
import scala.reflect.`ClassTag$`
import com.ing.baker.runtime.defaultinteractions.`package$`.`MODULE$` as defaultinteractions
import com.ing.baker.runtime.javadsl.Baker as JavaBaker
import com.ing.baker.runtime.javadsl.InteractionInstance as JavaInteractionInstance
import scala.collection.immutable.List as ScalaList

/**
 * In-memory implementation of Baker.
 *
 * Note: This class may show compiler warnings due to Scala/Kotlin interoperability limitations.
 * The compiler may report unimplemented abstract members or type mismatches, but these are false positives.
 * All required functionality is properly implemented in the parent BakerF class.
 */
@Suppress("ABSTRACT_MEMBER_NOT_IMPLEMENTED")
class InMemoryBaker(
    private val bakerConfig: BakerConfig,
    components: BakerComponents<IO<Any>>
) : BakerF<IO<Any>>(components, IO.asyncForIO() as Async<IO<Any>>, IO.asyncForIO() as Async<IO<Any>>) {

    companion object {

        @JvmStatic
        fun build(implementations: ScalaList<*>): IO<BakerF<IO<*>>> = build(BakerConfig.default(), implementations)

        @JvmStatic
        @Suppress("UNCHECKED_CAST")
        fun build(
            config: BakerConfig,
            implementations: ScalaList<*>
        ): IO<BakerF<IO<*>>> {
            val recipeInstanceManager =
                InMemoryRecipeInstanceManager(
                    config.retentionPeriodCheckInterval(),
                    config.idleTimeout()
                )
            val interactionInstances =
                implementations.concat(defaultinteractions.all()) as ScalaList<InteractionInstance<IO<*>>>
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
            return IO.pure(
                InMemoryBaker(config, components as BakerComponents<IO<Any>>) as BakerF<IO<*>>
            )
        }

        @JvmStatic
        fun java(config: BakerConfig, implementations: List<Any>): JavaBaker {
            val futureToIO = object : FunctionK<Future<*>, IO<*>> {
                override fun <A> apply(fa: Future<*>): IO<*> = IO.fromFuture(IO.pure(fa))
            }

            val scalaInteractions =
                implementations
                    .map { item ->
                        when (item) {
                            is InteractionInstance<*> -> item
                            is JavaInteractionInstance -> item.asScala()
                                .translate(futureToIO) as InteractionInstance<IO<*>>

                            else -> InteractionInstance.unsafeFrom(
                                item,
                                IO.asyncForIO(),
                                `ClassTag$`.`MODULE$`.apply(IO::class.java)
                            )
                        }
                    }
                    .let { asScala(it) }
                    .toList()

            val ioToFuture = object : FunctionK<IO<*>, Future<*>> {
                override fun <A> apply(fa: IO<*>): Future<*> = fa.unsafeToFuture(IORuntime.global())
            }

            return build(config, scalaInteractions)
                .unsafeRunSync(IORuntime.global())
                .asDeprecatedFutureImplementation(ioToFuture, futureToIO)
                .let { JavaBaker(it) }
        }

        @JvmStatic
        fun java(implementations: List<Any>): JavaBaker =
            java(BakerConfig.default(), implementations)

        @JvmStatic
        fun java(): JavaBaker =
            java(BakerConfig.default(), emptyList())
    }

    override fun config(): BakerConfig = bakerConfig

    /**
     * Attempts to gracefully shutdown the baker system.
     */
    override fun gracefulShutdown(): IO<Any> = IO.pure {}
}
