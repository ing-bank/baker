package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.catseffect.AsyncSupport
import com.ing.baker.runtime.catseffect.EffectSupport
import com.ing.baker.runtime.common.FunctionK
import com.ing.baker.runtime.model.InteractionInstance
import scala.concurrent.Future
import scala.jdk.javaapi.CollectionConverters.asScala
import scala.reflect.`ClassTag$`
import java.util.concurrent.CompletableFuture
import scala.collection.immutable.List as ScalaList
import scala.jdk.javaapi.FutureConverters.asJava as futureAsJava
import scala.jdk.javaapi.FutureConverters.asScala as futureAsScala
import scala.runtime.BoxedUnit

internal typealias InMemoryEffect<A> = CompletableFuture<A>

internal fun <A, B> InMemoryEffect<A>.map(f: (A) -> B): InMemoryEffect<B> =
    thenApply { value -> f(value) }

internal fun <A, B> InMemoryEffect<A>.flatMap(f: (A) -> InMemoryEffect<B>): InMemoryEffect<B> =
    thenCompose { value -> f(value) }

internal object InMemoryEffects {

    @Suppress("UNCHECKED_CAST")
    fun asyncSupportAny(): AsyncSupport<InMemoryEffect<Any>> =
        AsyncSupport.completableFutureSupport() as AsyncSupport<InMemoryEffect<Any>>

    @Suppress("UNCHECKED_CAST")
    fun effectSupportAny(): EffectSupport<InMemoryEffect<Any>> =
        EffectSupport.fromCompletableFuture() as EffectSupport<InMemoryEffect<Any>>

    @Suppress("UNCHECKED_CAST")
    fun classTagAny() = `ClassTag$`.`MODULE$`.apply<InMemoryEffect<Any>>(
        CompletableFuture::class.java as Class<InMemoryEffect<Any>>
    )

    fun <A> pure(value: A): InMemoryEffect<A> = CompletableFuture.completedFuture(value)

    @Suppress("UNCHECKED_CAST")
    fun unit(): InMemoryEffect<Any> = pure(BoxedUnit.UNIT) as InMemoryEffect<Any>

    fun <A> delay(thunk: () -> A): InMemoryEffect<A> =
        try {
            pure(thunk())
        } catch (throwable: Throwable) {
            val failed = CompletableFuture<A>()
            failed.completeExceptionally(throwable)
            failed
        }

    fun <A> defer(thunk: () -> InMemoryEffect<A>): InMemoryEffect<A> =
        try {
            thunk()
        } catch (throwable: Throwable) {
            val failed = CompletableFuture<A>()
            failed.completeExceptionally(throwable)
            failed
        }

    fun <A> runSync(io: InMemoryEffect<A>): A = io.join()

    fun futureToCompletableFuture(): FunctionK<Future<*>, InMemoryEffect<*>> =
        object : FunctionK<Future<*>, InMemoryEffect<*>> {
            override fun <A> apply(fa: Future<*>): InMemoryEffect<*> =
                futureAsJava(fa as Future<Any>).toCompletableFuture()
        }

    fun completableFutureToFuture(): FunctionK<InMemoryEffect<*>, Future<*>> =
        object : FunctionK<InMemoryEffect<*>, Future<*>> {
            override fun <A> apply(fa: InMemoryEffect<*>): Future<*> =
                futureAsScala(fa as CompletableFuture<Any>)
        }

    @Suppress("UNCHECKED_CAST")
    fun toScalaCompletableFutureInteractions(implementations: List<Any>): ScalaList<InteractionInstance<InMemoryEffect<*>>> {
        val futureToCompletableFuture = futureToCompletableFuture()
        return implementations
            .map { item ->
                when (item) {
                    is InteractionInstance<*> -> item
                    is com.ing.baker.runtime.javadsl.InteractionInstance ->
                        item.asScala().translate(futureToCompletableFuture) as InteractionInstance<InMemoryEffect<*>>

                    else -> InteractionInstance.unsafeFrom(
                        item,
                        effectSupportAny(),
                        `ClassTag$`.`MODULE$`.apply(CompletableFuture::class.java)
                    )
                }
            }
            .let { asScala(it) }
            .toList()
            as ScalaList<InteractionInstance<InMemoryEffect<*>>>
    }
}

