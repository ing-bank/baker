package com.ing.baker.runtime.inmemory

import cats.effect.IO
import cats.effect.unsafe.IORuntime
import com.ing.baker.runtime.catseffect.AsyncSupport
import com.ing.baker.runtime.catseffect.EffectSupport
import com.ing.baker.runtime.common.FunctionK
import com.ing.baker.runtime.model.InteractionInstance
import scala.concurrent.Future
import scala.jdk.javaapi.CollectionConverters.asScala
import scala.reflect.`ClassTag$`
import scala.collection.immutable.List as ScalaList
import scala.jdk.javaapi.FutureConverters.asJava as futureAsJava

internal typealias InMemoryEffect<A> = IO<A>

internal object InMemoryEffects {

    private val runtime: IORuntime = IORuntime.global()

    @Suppress("UNCHECKED_CAST")
    fun asyncSupportAny(): AsyncSupport<InMemoryEffect<Any>> =
        AsyncSupport.fromIO(runtime) as AsyncSupport<InMemoryEffect<Any>>

    @Suppress("UNCHECKED_CAST")
    fun effectSupportAny(): EffectSupport<InMemoryEffect<Any>> =
        EffectSupport.fromApplicative(IO.asyncForIO()) as EffectSupport<InMemoryEffect<Any>>

    @Suppress("UNCHECKED_CAST")
    fun classTagAny() = `ClassTag$`.`MODULE$`.apply<InMemoryEffect<Any>>(
        IO::class.java as Class<InMemoryEffect<Any>>
    )

    fun <A> pure(value: A): InMemoryEffect<A> = IO.pure(value)

    @Suppress("UNCHECKED_CAST")
    fun unit(): InMemoryEffect<Any> = IO.unit() as InMemoryEffect<Any>

    fun <A> delay(thunk: () -> A): InMemoryEffect<A> = IO.delay { thunk() }

    fun <A> defer(thunk: () -> InMemoryEffect<A>): InMemoryEffect<A> = IO.defer { thunk() }

    fun <A> runSync(io: InMemoryEffect<A>): A = io.unsafeRunSync(runtime)

    fun futureToIO(): FunctionK<Future<*>, InMemoryEffect<*>> =
        object : FunctionK<Future<*>, InMemoryEffect<*>> {
            override fun <A> apply(fa: Future<*>): InMemoryEffect<*> = IO.fromFuture(IO.pure(fa))
        }

    fun ioToFuture(): FunctionK<InMemoryEffect<*>, Future<*>> =
        object : FunctionK<InMemoryEffect<*>, Future<*>> {
            override fun <A> apply(fa: InMemoryEffect<*>): Future<*> = fa.unsafeToFuture(runtime)
        }

    fun <A> ioToCompletableFuture(io: InMemoryEffect<A>) =
        futureAsJava(io.unsafeToFuture(runtime)).toCompletableFuture()

    @Suppress("UNCHECKED_CAST")
    fun toScalaIoInteractions(implementations: List<Any>): ScalaList<InteractionInstance<InMemoryEffect<*>>> {
        val futureToIO = futureToIO()
        return implementations
            .map { item ->
                when (item) {
                    is InteractionInstance<*> -> item
                    is com.ing.baker.runtime.javadsl.InteractionInstance ->
                        item.asScala().translate(futureToIO) as InteractionInstance<InMemoryEffect<*>>

                    else -> InteractionInstance.unsafeFrom(
                        item,
                        effectSupportAny(),
                        `ClassTag$`.`MODULE$`.apply(IO::class.java)
                    )
                }
            }
            .let { asScala(it) }
            .toList()
            as ScalaList<InteractionInstance<InMemoryEffect<*>>>
    }
}

