@file:OptIn(ExperimentalStdlibApi::class, ExperimentalReflectionOnLambdas::class)

package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.javadsl.InteractionInstanceInput
import com.ing.baker.types.Converters
import scala.collection.immutable.Map
import java.util.*
import java.util.concurrent.CompletableFuture
import kotlin.reflect.full.createType
import kotlin.reflect.jvm.ExperimentalReflectionOnLambdas
import kotlin.reflect.jvm.javaType
import kotlin.reflect.jvm.reflect

inline fun <reified T1, R> functionInteractionInstance(
    name: String,
    noinline function: (T1) -> R
): InteractionInstance {

    val types = listOf(
        T1::class.createType().javaType
    )

    val params = function.reflect()?.parameters ?: error("Cannot read parameters")

    return object : InteractionInstance() {

        override fun execute(
            input: MutableList<IngredientInstance>, metadata: Map<String, String>
        ): CompletableFuture<Optional<EventInstance>> {
            return run(input)
        }

        override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
            TODO("Not yet implemented")
        }

        override fun input(): List<InteractionInstanceInput> =
            types
                .zip(params)
                .map { (type, param) ->
                    InteractionInstanceInput(
                        Optional.ofNullable(param.name),
                        Converters.readJavaType(type)
                    )
                }

        override fun name(): String {
            return "\$SieveInteraction\$${name}" ?: error("Cannot read class name")
        }

        override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
            try {
                val args = types
                    .zip(input.toList()) { type, param -> param.value.`as`(type) }
                    .toTypedArray()
                val res = function.invoke(
                    args[0] as T1
                )
                val event = EventInstance.from(mapOf(name to res))
                val eventInstance = EventInstance("\$SieveEvent\$$name", event.providedIngredients)
                return CompletableFuture.completedFuture(Optional.ofNullable(eventInstance))
            } catch (e: Exception) {
                return CompletableFuture.failedFuture(e)
            }
        }
    }
}

inline fun <reified T1, reified T2, R> functionInteractionInstance(
    name: String,
    noinline function: (T1, T2) -> R
): InteractionInstance {

    val types = listOf(
        T1::class.createType().javaType,
        T2::class.createType().javaType
    )

    val params = function.reflect()?.parameters ?: error("Cannot read parameters")

    return object : InteractionInstance() {

        override fun execute(
            input: MutableList<IngredientInstance>, metadata: Map<String, String>
        ): CompletableFuture<Optional<EventInstance>> {
            return run(input)
        }

        override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
            TODO("Not yet implemented")
        }

        override fun input(): List<InteractionInstanceInput> =
            types
                .zip(params)
                .map { (type, param) ->
                    InteractionInstanceInput(
                        Optional.ofNullable(param.name),
                        Converters.readJavaType(type)
                    )
                }

        override fun name(): String {
            return "\$SieveInteraction\$${name}" ?: error("Cannot read class name")
        }

        override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
            try {
                val args = types
                    .zip(input.toList()) { type, param -> param.value.`as`(type) }
                    .toTypedArray()
                val res = function.invoke(
                    args[0] as T1,
                    args[1] as T2
                )
                val event = EventInstance.from(mapOf(name to res))
                val eventInstance = EventInstance("\$SieveEvent\$$name", event.providedIngredients)
                return CompletableFuture.completedFuture(Optional.ofNullable(eventInstance))
            } catch (e: Exception) {
                return CompletableFuture.failedFuture(e)
            }
        }
    }
}

inline fun <reified T1, reified T2, reified T3, R> functionInteractionInstance(
    name: String,
    noinline function: (T1, T2, T3) -> R
): InteractionInstance {

    val types = listOf(
        T1::class.createType().javaType,
        T2::class.createType().javaType,
        T3::class.createType().javaType,
    )

    val params = function.reflect()?.parameters ?: error("Cannot read parameters")

    return object : InteractionInstance() {

        override fun execute(
            input: MutableList<IngredientInstance>, metadata: Map<String, String>
        ): CompletableFuture<Optional<EventInstance>> {
            return run(input)
        }

        override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
            TODO("Not yet implemented")
        }

        override fun input(): List<InteractionInstanceInput> =
            types
                .zip(params)
                .map { (type, param) ->
                    InteractionInstanceInput(
                        Optional.ofNullable(param.name),
                        Converters.readJavaType(type)
                    )
                }

        override fun name(): String {
            return "\$SieveInteraction\$${name}" ?: error("Cannot read class name")
        }

        override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
            try {
                val args = types
                    .zip(input.toList()) { type, param -> param.value.`as`(type) }
                    .toTypedArray()
                val res = function.invoke(
                    args[0] as T1,
                    args[1] as T2,
                    args[2] as T3,
                )
                val event = EventInstance.from(mapOf(name to res))
                val eventInstance = EventInstance("\$SieveEvent\$$name", event.providedIngredients)
                return CompletableFuture.completedFuture(Optional.ofNullable(eventInstance))
            } catch (e: Exception) {
                return CompletableFuture.failedFuture(e)
            }
        }
    }
}