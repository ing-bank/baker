package com.ing.baker.recipe.wirespec

import arrow.core.NonEmptyList
import community.flock.wirespec.compiler.core.FileUri
import community.flock.wirespec.compiler.core.parse.ast.*
import community.flock.wirespec.compiler.core.parse.ast.Reference.Primitive.Type.Precision
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class BakerKotlinEmitterTest {

    private val emitter = BakerKotlinEmitter()

    // Workaround for Kotlin name collision: Reference.Primitive.Type.Boolean clashes with kotlin.Boolean
    private val BOOLEAN_TYPE: Reference.Primitive.Type =
        Class.forName("community.flock.wirespec.compiler.core.parse.ast.Reference\$Primitive\$Type\$Boolean")
            .getField("INSTANCE").get(null) as Reference.Primitive.Type

    // Helper to create a Type definition
    private fun type(name: String, vararg fields: Field): Type =
        Type(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier(name),
            shape = Type.Shape(fields.toList()),
            extends = emptyList()
        )

    // Helper to create a Field
    private fun field(name: String, ref: Reference): Field =
        Field(emptyList(), FieldIdentifier(name), ref)

    // Helper to create a Module with definitions and set it on the emitter
    private fun setModuleWithTypes(vararg definitions: Definition) {
        val module = Module(
            fileUri = FileUri("test.ws"),
            statements = NonEmptyList(definitions.first(), definitions.drop(1))
        )
        emitter.setModule(module)
    }

    @Test
    fun emitSimpleGetEndpoint() {
        // Define the types used in responses
        val todoDtoType = type(
            "TodoDto",
            field("id", Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P64, null), false)),
            field("title", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("completed", Reference.Primitive(BOOLEAN_TYPE, false))
        )
        val errorDtoType = type(
            "ErrorDto",
            field("code", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("message", Reference.Primitive(Reference.Primitive.Type.String(null), false))
        )

        // GET /todos/{id: Integer} -> { 200 -> TodoDto, 404 -> ErrorDto }
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("GetTodo"),
            method = Endpoint.Method.GET,
            path = listOf(
                Endpoint.Segment.Literal("/todos/"),
                Endpoint.Segment.Param(
                    FieldIdentifier("id"),
                    Reference.Primitive(
                        Reference.Primitive.Type.Integer(Precision.P64, null),
                        false
                    )
                )
            ),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response(
                    "200",
                    emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("TodoDto", false)),
                    emptyList()
                ),
                Endpoint.Response(
                    "404",
                    emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("ErrorDto", false)),
                    emptyList()
                )
            )
        )

        setModuleWithTypes(todoDtoType, errorDtoType, endpoint)

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction
            import kotlinx.coroutines.runBlocking

            interface GetTodoInteraction : Interaction {
                sealed interface GetTodoOutcome
                data class GetTodoResponse200(val id: Long, val title: String, val completed: Boolean) : GetTodoOutcome
                data class GetTodoResponse404(val code: String, val message: String) : GetTodoOutcome

                fun apply(id: Long): GetTodoOutcome
            }

            class GetTodoInteractionImpl(
                private val client: GetTodo.Handler
            ) : GetTodoInteraction {
                override fun apply(id: Long): GetTodoInteraction.GetTodoOutcome {
                    val request = GetTodo.Request(id)
                    val response = runBlocking { client.getTodo(request) }
                    return when (response) {
                        is GetTodo.Response200 -> GetTodoInteraction.GetTodoResponse200(id = response.body.id, title = response.body.title, completed = response.body.completed)
                        is GetTodo.Response404 -> GetTodoInteraction.GetTodoResponse404(code = response.body.code, message = response.body.message)
                    }
                }
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }

    @Test
    fun emitPostEndpointWithBody() {
        // Define the types used in request and responses
        val createTodoRequestType = type(
            "CreateTodoRequest",
            field("title", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("completed", Reference.Primitive(BOOLEAN_TYPE, false))
        )
        val todoDtoType = type(
            "TodoDto",
            field("id", Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P64, null), false)),
            field("title", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("completed", Reference.Primitive(BOOLEAN_TYPE, false))
        )
        val errorDtoType = type(
            "ErrorDto",
            field("code", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("message", Reference.Primitive(Reference.Primitive.Type.String(null), false))
        )

        // POST /todos CreateTodoRequest -> { 201 -> TodoDto, 400 -> ErrorDto }
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("CreateTodo"),
            method = Endpoint.Method.POST,
            path = listOf(Endpoint.Segment.Literal("/todos")),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(
                Endpoint.Request(
                    Endpoint.Content("application/json", Reference.Custom("CreateTodoRequest", false))
                )
            ),
            responses = listOf(
                Endpoint.Response(
                    "201",
                    emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("TodoDto", false)),
                    emptyList()
                ),
                Endpoint.Response(
                    "400",
                    emptyList(),
                    Endpoint.Content("application/json", Reference.Custom("ErrorDto", false)),
                    emptyList()
                )
            )
        )

        setModuleWithTypes(createTodoRequestType, todoDtoType, errorDtoType, endpoint)

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction
            import kotlinx.coroutines.runBlocking

            interface CreateTodoInteraction : Interaction {
                sealed interface CreateTodoOutcome
                data class CreateTodoResponse201(val id: Long, val title: String, val completed: Boolean) : CreateTodoOutcome
                data class CreateTodoResponse400(val code: String, val message: String) : CreateTodoOutcome

                fun apply(title: String, completed: Boolean): CreateTodoOutcome
            }

            class CreateTodoInteractionImpl(
                private val client: CreateTodo.Handler
            ) : CreateTodoInteraction {
                override fun apply(title: String, completed: Boolean): CreateTodoInteraction.CreateTodoOutcome {
                    val body = CreateTodoRequest(title = title, completed = completed)
                    val request = CreateTodo.Request(body)
                    val response = runBlocking { client.createTodo(request) }
                    return when (response) {
                        is CreateTodo.Response201 -> CreateTodoInteraction.CreateTodoResponse201(id = response.body.id, title = response.body.title, completed = response.body.completed)
                        is CreateTodo.Response400 -> CreateTodoInteraction.CreateTodoResponse400(code = response.body.code, message = response.body.message)
                    }
                }
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }

    @Test
    fun emitEndpointWithQueryParams() {
        // Define the type used in response
        val todoDtoType = type(
            "TodoDto",
            field("id", Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P64, null), false)),
            field("title", Reference.Primitive(Reference.Primitive.Type.String(null), false)),
            field("completed", Reference.Primitive(BOOLEAN_TYPE, false))
        )

        // GET /todos ? search: String, limit: Integer -> { 200 -> TodoDto[] }
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("ListTodos"),
            method = Endpoint.Method.GET,
            path = listOf(Endpoint.Segment.Literal("/todos")),
            queries = listOf(
                Field(
                    emptyList(),
                    FieldIdentifier("search"),
                    Reference.Primitive(Reference.Primitive.Type.String(null), false)
                ),
                Field(
                    emptyList(),
                    FieldIdentifier("limit"),
                    Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P32, null), false)
                )
            ),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response(
                    "200",
                    emptyList(),
                    Endpoint.Content(
                        "application/json",
                        Reference.Iterable(Reference.Custom("TodoDto", false), false)
                    ),
                    emptyList()
                )
            )
        )

        setModuleWithTypes(todoDtoType, endpoint)

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction
            import kotlinx.coroutines.runBlocking

            interface ListTodosInteraction : Interaction {
                sealed interface ListTodosOutcome
                data class ListTodosResponse200(val body: List<TodoDto>) : ListTodosOutcome

                fun apply(search: String, limit: Int): ListTodosOutcome
            }

            class ListTodosInteractionImpl(
                private val client: ListTodos.Handler
            ) : ListTodosInteraction {
                override fun apply(search: String, limit: Int): ListTodosInteraction.ListTodosOutcome {
                    val request = ListTodos.Request(search, limit)
                    val response = runBlocking { client.listTodos(request) }
                    return when (response) {
                        is ListTodos.Response200 -> ListTodosInteraction.ListTodosResponse200(response.body)
                    }
                }
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }

    @Test
    fun emitEndpointWithNoBodyResponse() {
        // DELETE /todos/{id} -> { 204 -> (no body) }
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("DeleteTodo"),
            method = Endpoint.Method.DELETE,
            path = listOf(
                Endpoint.Segment.Literal("/todos/"),
                Endpoint.Segment.Param(
                    FieldIdentifier("id"),
                    Reference.Primitive(
                        Reference.Primitive.Type.Integer(Precision.P64, null),
                        false
                    )
                )
            ),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response("204", emptyList(), null, emptyList())
            )
        )

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction
            import kotlinx.coroutines.runBlocking

            interface DeleteTodoInteraction : Interaction {
                sealed interface DeleteTodoOutcome
                data object DeleteTodoResponse204 : DeleteTodoOutcome

                fun apply(id: Long): DeleteTodoOutcome
            }

            class DeleteTodoInteractionImpl(
                private val client: DeleteTodo.Handler
            ) : DeleteTodoInteraction {
                override fun apply(id: Long): DeleteTodoInteraction.DeleteTodoOutcome {
                    val request = DeleteTodo.Request(id)
                    val response = runBlocking { client.deleteTodo(request) }
                    return when (response) {
                        is DeleteTodo.Response204 -> DeleteTodoInteraction.DeleteTodoResponse204
                    }
                }
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }
}
