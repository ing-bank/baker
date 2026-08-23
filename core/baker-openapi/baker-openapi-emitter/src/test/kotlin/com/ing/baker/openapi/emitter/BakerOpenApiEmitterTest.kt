package com.ing.baker.openapi.emitter

import arrow.core.NonEmptyList
import community.flock.wirespec.compiler.core.FileUri
import community.flock.wirespec.compiler.core.emit.PackageName
import community.flock.wirespec.compiler.core.parse.ast.DefinitionIdentifier
import community.flock.wirespec.compiler.core.parse.ast.Endpoint
import community.flock.wirespec.compiler.core.parse.ast.Field
import community.flock.wirespec.compiler.core.parse.ast.FieldIdentifier
import community.flock.wirespec.compiler.core.parse.ast.Module
import community.flock.wirespec.compiler.core.parse.ast.Reference
import community.flock.wirespec.compiler.core.parse.ast.Type
import community.flock.wirespec.compiler.utils.Logger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class BakerOpenApiEmitterTest {

    private val emitter = BakerOpenApiEmitter(PackageName("com.example.generated"))
    private val logger = object : Logger(Logger.Level.ERROR) {
        override fun debug(s: String) = Unit
        override fun info(s: String) = Unit
        override fun warn(s: String) = Unit
        override fun error(s: String) = Unit
    }

    private fun field(name: String, ref: Reference) = Field(emptyList(), FieldIdentifier(name), ref)
    private fun primString() = Reference.Primitive(Reference.Primitive.Type.String(null), false)

    @Test
    fun `emits an object implementing ApiOperation for a POST endpoint with body`() {
        val userType = Type(
            null, emptyList(),
            DefinitionIdentifier("UserDto"),
            Type.Shape(listOf(field("firstName", primString()), field("email", primString()))),
            emptyList(),
        )
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("CreateUser"),
            method = Endpoint.Method.POST,
            path = listOf(Endpoint.Segment.Literal("/users")),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(
                Endpoint.Request(Endpoint.Content("application/json", Reference.Custom("UserDto", false)))
            ),
            responses = listOf(
                Endpoint.Response("201", emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("UserDto", false)),
                    emptyList()),
                Endpoint.Response("400", emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("UserDto", false)),
                    emptyList()),
            ),
        )
        val module = Module(FileUri("test.ws"), NonEmptyList(userType, listOf(endpoint)))

        val emitted = emitter.emit(endpoint, module, logger)

        val src = emitted.result
        assertTrue(src.contains("package com.example.generated.api"), src)
        assertTrue(src.contains("import com.ing.baker.openapi.dsl.ApiOperation"), src)
        assertTrue(src.contains("import com.ing.baker.openapi.dsl.InputField"), src)
        assertTrue(src.contains("import com.example.generated.endpoint.CreateUser"), src)
        assertTrue(src.contains("object CreateUser : ApiOperation"), src)
        assertTrue(src.contains("override val operationName = \"CreateUser\""), src)
        assertTrue(src.contains("InputField(\"firstName\", String::class)"), src)
        assertTrue(src.contains("InputField(\"email\", String::class)"), src)
        assertTrue(src.contains("201 to CreateUser.Response201::class"), src)
        assertTrue(src.contains("400 to CreateUser.Response400::class"), src)
        assertTrue(src.contains("override val handlerClass = CreateUser.Handler::class"), src)
        assertEquals("com/example/generated/api/CreateUser", emitted.file)
    }

    @Test
    fun `emits InputField for path parameters`() {
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("GetUser"),
            method = Endpoint.Method.GET,
            path = listOf(
                Endpoint.Segment.Literal("/users/"),
                Endpoint.Segment.Param(FieldIdentifier("id"), primString()),
            ),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response("200", emptyList(), null, emptyList())
            ),
        )
        val module = Module(FileUri("test.ws"), NonEmptyList(endpoint, emptyList()))

        val src = emitter.emit(endpoint, module, logger).result
        assertTrue(src.contains("InputField(\"id\", String::class)"), src)
    }
}
