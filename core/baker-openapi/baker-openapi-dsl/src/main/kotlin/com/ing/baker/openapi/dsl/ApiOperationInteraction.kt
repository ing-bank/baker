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

typealias ResponseMapper = (Wirespec.Response<*>) -> Any

class ApiOperationInteraction(
    private val operation: ApiOperation,
    private val handler: Wirespec.Handler,
    private val mappers: kotlin.collections.Map<Int, ResponseMapper>,
) : InteractionInstance() {

    override fun name(): String = operation.operationName

    override fun input(): MutableList<InteractionInstanceInput> =
        operation.inputFields
            .map { field ->
                InteractionInstanceInput(
                    Optional.of(field.name),
                    Converters.readJavaType(field.type.java),
                )
            }
            .toMutableList()

    override fun execute(
        input: MutableList<IngredientInstance>,
        metadata: Map<String, String>,
    ): CompletableFuture<Optional<EventInstance>> = run(input)

    override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
        throw UnsupportedOperationException("ApiOperationInteraction does not support single-input execute()")
    }

    override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
        return try {
            val ingredientMap: kotlin.collections.Map<String, Any?> =
                input.associate { it.name to it.value.`as`(operation.inputFieldType(it.name)) }
            val request = operation.buildRequest(ingredientMap)
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

private fun ApiOperation.inputFieldType(name: String): java.lang.reflect.Type =
    inputFields.first { it.name == name }.type.java
