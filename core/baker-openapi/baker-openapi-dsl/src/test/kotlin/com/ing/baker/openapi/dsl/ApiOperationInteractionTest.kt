package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.types.PrimitiveValue
import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import java.util.concurrent.ExecutionException
import kotlin.reflect.KClass

private class FakeHandler : Wirespec.Handler

private object FakeHeaders : Wirespec.Response.Headers

private class FakeResponse(
    override val status: Int,
    override val body: Map<String, Any?>,
) : Wirespec.Response<Map<String, Any?>> {
    override val headers: Wirespec.Response.Headers = FakeHeaders
}

private data class UserCreated(val id: String, val email: String)

private class FakeOperation(
    private val nextResponse: Wirespec.Response<*>,
) : ApiOperation<Unit> {
    override val operationName: String = "CreateUser"
    override val inputFields = listOf(
        InputField("firstName", String::class),
        InputField("email", String::class),
    )
    override val responseTypes: Map<Int, KClass<*>> = mapOf(
        201 to FakeResponse::class,
        400 to FakeResponse::class,
    )
    override val handlerClass: KClass<out Wirespec.Handler> = FakeHandler::class
    var capturedRequest: Map<String, Any?>? = null
    override fun buildRequest(ingredients: Map<String, Any?>): Any {
        capturedRequest = ingredients
        return ingredients
    }
    override fun buildRequestFromBody(body: Unit): Any = body
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> = nextResponse
    override fun buildHandler(
        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,
        serialization: Wirespec.Serialization,
    ): Wirespec.Handler = FakeHandler()
}

private val emptyScalaMetadata: scala.collection.immutable.Map<String, String> =
    scala.collection.immutable.`Map$`.`MODULE$`.empty<String, String>() as scala.collection.immutable.Map<String, String>

class ApiOperationInteractionTest {

    @Test
    fun `name returns operationName`() {
        val op = FakeOperation(FakeResponse(201, emptyMap()))
        val interaction = ApiOperationInteraction(op, FakeHandler(), emptyMap())
        assertEquals("CreateUser", interaction.name())
    }

    @Test
    fun `input returns one InteractionInstanceInput per input field`() {
        val op = FakeOperation(FakeResponse(201, emptyMap()))
        val interaction = ApiOperationInteraction(op, FakeHandler(), emptyMap())
        val inputs = interaction.input()
        assertEquals(2, inputs.size)
        assertEquals("firstName", inputs[0].name.orElseThrow())
        assertEquals("email", inputs[1].name.orElseThrow())
    }

    @Test
    fun `execute routes 201 through configured mapper and returns the fired event`() {
        val op = FakeOperation(FakeResponse(201, mapOf("id" to "u1", "email" to "a@b")))
        val mapper: (Wirespec.Response<*>) -> Any = { resp ->
            val body = (resp as FakeResponse).body
            UserCreated(id = body["id"] as String, email = body["email"] as String)
        }
        val interaction = ApiOperationInteraction(op, FakeHandler(), mapOf(201 to mapper))

        val result = interaction.execute(
            mutableListOf(
                IngredientInstance("firstName", PrimitiveValue("John")),
                IngredientInstance("email", PrimitiveValue("a@b")),
            ),
            emptyScalaMetadata,
        ).get()

        assertTrue(result.isPresent)
        assertEquals("UserCreated", result.get().name)
        assertEquals(mapOf("firstName" to "John", "email" to "a@b"), op.capturedRequest)
    }

    @Test
    fun `execute fails the future on unmapped status`() {
        val op = FakeOperation(FakeResponse(500, emptyMap<String, Any?>()))
        val interaction = ApiOperationInteraction(
            op,
            FakeHandler(),
            mapOf(201 to { _ -> UserCreated("x", "y") })
        )

        val ex = assertThrows<ExecutionException> {
            interaction.execute(
                mutableListOf(
                    IngredientInstance("firstName", PrimitiveValue("John")),
                    IngredientInstance("email", PrimitiveValue("a@b")),
                ),
                emptyScalaMetadata,
            ).get()
        }
        assertNotNull(ex.cause)
        val msg = ex.cause!!.message ?: ""
        assertTrue(msg.contains("500"), "expected message to mention status 500, was: $msg")
        assertTrue(msg.contains("CreateUser"), "expected message to mention operation, was: $msg")
    }
}
