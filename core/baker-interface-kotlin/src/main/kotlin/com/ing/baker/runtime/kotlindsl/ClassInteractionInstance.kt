@file:OptIn(ExperimentalStdlibApi::class)

package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.javadsl.InteractionInstanceInput
import com.ing.baker.types.Converters
import scala.collection.immutable.Map
import java.util.Optional
import java.util.concurrent.CompletableFuture
import kotlin.reflect.full.createInstance
import kotlin.reflect.full.functions
import kotlin.reflect.javaType
import kotlin.reflect.jvm.javaMethod

inline fun <reified T: Any> classInteractionInstance(): InteractionInstance {

    return object : InteractionInstance() {

        val function = T::class.functions.single { it.name == "apply" }

        override fun execute(
            input: MutableList<IngredientInstance>, metadata: Map<String, String>
        ): CompletableFuture<Optional<EventInstance>> {
            return run(input)
        }

        override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
            TODO("Not yet implemented")
        }


        override fun input(): List<InteractionInstanceInput> {
            return function.parameters.drop(1)
                .map {
                    InteractionInstanceInput(
                        Optional.ofNullable(it.name),
                        Converters.readJavaType(it.type.javaType)
                    )
                }
                .toList()
        }

        override fun name(): String {
            return T::class.simpleName ?: error("Cannot read class name")
        }

        override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
            try {
                val instance = T::class.createInstance()
                val args = function
                    .javaMethod
                    ?.genericParameterTypes
                    ?.zip(input.toList()) { type, param ->
                        param.value.`as`(type)
                    }
                    .orEmpty()
                    .toTypedArray()
                val res = function.call(instance, *args)
                val event = EventInstance.from(res)
                return CompletableFuture.completedFuture(Optional.ofNullable(event))
            } catch (e: Exception) {
                return CompletableFuture.failedFuture(e)
            }
        }
    }
}
