package com.ing.baker.runtime.kotlindsl

import com.ing.baker.recipe.kotlindsl.Recipe
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.javadsl.InteractionInstanceInput
import com.ing.baker.types.Converters
import scala.collection.Seq
import scala.collection.immutable.Map
import java.util.*
import java.util.concurrent.CompletableFuture
import kotlin.reflect.jvm.javaType
import kotlin.reflect.jvm.reflect
import kotlin.reflect.typeOf

@OptIn(kotlin.reflect.jvm.ExperimentalReflectionOnLambdas::class)
class FunctionInteractionInstance<R>(private val types: List<java.lang.reflect.Type>, val function: Function<R>, private val name: String): InteractionInstance() {
    private val params = function.reflect()?.parameters ?: error("Cannot read parameters")

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
            val res = when (args.size) {
                1 -> (function as Function1<Any, R>).invoke(args[0])
                2 -> (function as Function2<Any, Any, R>).invoke(args[0], args[1])
                3 -> (function as Function3<Any, Any, Any, R>).invoke(args[0], args[1], args[2])
                else -> throw IllegalStateException("More than 3 parameters not supported")
            }
            val event = EventInstance.from(mapOf(name to res))
            val eventInstance = EventInstance("\$SieveEvent\$$name", event.providedIngredients)
            return CompletableFuture.completedFuture(Optional.ofNullable(eventInstance))
        } catch (e: Exception) {
            return CompletableFuture.failedFuture(e)
        }
    }
}

fun Recipe.sieveInstances(): List<InteractionInstance> = sieves().asJava.map { sieve ->
    FunctionInteractionInstance(sieve.javaTypes().asJava, sieve.function() as Function<*>, sieve.name())
} + subRecipes().asJava.filterIsInstance<Recipe>().flatMap(Recipe::sieveInstances)

val <T: Any> scala.collection.Seq<T>.asJava get() = scala.jdk.CollectionConverters.SeqHasAsJava(this).asJava()
val <T: Any> scala.collection.Set<T>.asJava get() = scala.jdk.CollectionConverters.SetHasAsJava(this).asJava()

inline fun <reified T1, R> functionInteractionInstance(
    name: String,
    noinline function: (T1) -> R
): InteractionInstance {

    val types = listOf(
        javaTypeOf<T1>(),
    )

    return FunctionInteractionInstance(types, function, name)
}

inline fun <reified T1, reified T2, R> functionInteractionInstance(
    name: String,
    noinline function: (T1, T2) -> R
): InteractionInstance {

    val types = listOf(
        javaTypeOf<T1>(),
        javaTypeOf<T2>(),
    )

    return FunctionInteractionInstance(types, function, name)
}

inline fun <reified T1, reified T2, reified T3, R> functionInteractionInstance(
    name: String,
    noinline function: (T1, T2, T3) -> R
): InteractionInstance {

    val types = listOf(
        javaTypeOf<T1>(),
        javaTypeOf<T2>(),
        javaTypeOf<T3>(),
    )

    return FunctionInteractionInstance(types, function, name)
}

inline fun <reified T> javaTypeOf() = typeOf<T>().javaType