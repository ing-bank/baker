package com.ing.baker.openapi.dsl

import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import kotlin.reflect.KClass

private class BindingStubHandler : Wirespec.Handler
private object BindingStubHeaders : Wirespec.Response.Headers
private class BindingStubResponse(override val status: Int) : Wirespec.Response<Unit> {
    override val body: Unit = Unit
    override val headers: Wirespec.Response.Headers = BindingStubHeaders
}

private object StubOp : ApiOperation {
    override val operationName = "Stub"
    override val inputFields: List<InputField> = emptyList()
    override val responseTypes: Map<Int, KClass<*>> = mapOf(200 to BindingStubResponse::class)
    override val handlerClass = BindingStubHandler::class
    override fun buildRequest(ingredients: Map<String, Any?>): Any = Unit
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> =
        BindingStubResponse(200)
}

class ApiOperationBindingTest {

    @Test
    fun `binding produces an ApiOperationInteraction with the operation name`() {
        val handler = BindingStubHandler()
        val binding = ApiOperationBinding(StubOp, handler, mappers = mapOf(200 to { _ -> "ok" }))
        val interaction = binding.toInteractionInstance()
        assertEquals("Stub", interaction.name())
    }
}
