package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.javadsl.InteractionInstanceInput
import com.ing.baker.types.Converters
import community.flock.wirespec.kotlin.Wirespec
import kotlinx.coroutines.runBlocking
import scala.collection.immutable.Map
import java.util.Optional
import java.util.concurrent.CompletableFuture
import kotlin.reflect.KClass
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.javaType

typealias ResponseMapper = (Wirespec.Response<*>) -> Any

class ApiOperationInteraction(
    private val operation: ApiOperation<*>,
    private val handler: Wirespec.Handler,
    private val mappers: kotlin.collections.Map<Int, ResponseMapper>,
    /**
     * Map from API field name → recipe ingredient name. Used only in the flat
     * ingredient flow.
     */
    private val nameOverrides: kotlin.collections.Map<String, String> = emptyMap(),
    /** Set when the recipe used the typed `inputFrom<E, R>(mapper)` flow. */
    private val inputEventClass: KClass<*>? = null,
    /** Reconstructed-event → wirespec body. Set when [inputEventClass] is set. */
    private val inputMapper: ((Any) -> Any)? = null,
) : InteractionInstance() {

    private val recipeToApi: kotlin.collections.Map<String, String> =
        nameOverrides.entries.associate { (api, recipe) -> recipe to api }

    /**
     * Declared ingredients depend on which input flow the recipe chose:
     * - Typed flow: the input event's primary-constructor parameters.
     * - Flat flow:  the API descriptor's inputFields.
     */
    private val declaredInputs: List<InteractionInstanceInput> =
        inputEventClass?.let { evt ->
            evt.primaryConstructor?.parameters?.map { p ->
                InteractionInstanceInput(
                    Optional.of(p.name!!),
                    Converters.readJavaType(p.type.javaType),
                )
            } ?: emptyList()
        } ?: operation.inputFields.map { field ->
            InteractionInstanceInput(
                Optional.of(field.name),
                Converters.readJavaType(field.type.java),
            )
        }

    override fun name(): String = operation.operationName

    override fun input(): MutableList<InteractionInstanceInput> = declaredInputs.toMutableList()

    override fun execute(
        input: MutableList<IngredientInstance>,
        metadata: Map<String, String>,
    ): CompletableFuture<Optional<EventInstance>> = run(input)

    override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
        throw UnsupportedOperationException("ApiOperationInteraction does not support single-input execute()")
    }

    override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
        return try {
            val request: Any = if (inputEventClass != null && inputMapper != null) {
                val event = reconstructInputEvent(inputEventClass, input)
                val body = inputMapper.invoke(event)
                @Suppress("UNCHECKED_CAST")
                (operation as ApiOperation<Any>).buildRequestFromBody(body)
            } else {
                val ingredientMap: kotlin.collections.Map<String, Any?> =
                    input.associate { instance ->
                        val apiName = recipeToApi[instance.name] ?: instance.name
                        apiName to instance.value.`as`(operation.inputFieldType(apiName))
                    }
                operation.buildRequest(ingredientMap)
            }
            val response = runBlocking { operation.invoke(handler, request) }
            val mapper = mappers[response.status]
                ?: error("No mapping configured for status ${response.status} on operation ${operation.operationName}")
            val event = mapper(response)
            CompletableFuture.completedFuture(Optional.ofNullable(EventInstance.from(event)))
        } catch (e: Exception) {
            CompletableFuture.failedFuture(e)
        }
    }
}

private fun reconstructInputEvent(eventClass: KClass<*>, input: List<IngredientInstance>): Any {
    val ctor = eventClass.primaryConstructor
        ?: error("Input event class ${eventClass.simpleName} has no primary constructor")
    val byName = input.associate { it.name to it }
    val args = ctor.parameters.map { p ->
        val instance = byName[p.name]
            ?: error("Missing ingredient '${p.name}' to reconstruct ${eventClass.simpleName}")
        instance.value.`as`(p.type.javaType)
    }
    return ctor.call(*args.toTypedArray())
}

private fun ApiOperation<*>.inputFieldType(name: String): java.lang.reflect.Type =
    inputFields.first { it.name == name }.type.java
