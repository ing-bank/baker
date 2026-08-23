package com.ing.baker.recipe.wirespec

import community.flock.wirespec.compiler.core.parse.ast.*
import community.flock.wirespec.compiler.core.parse.ast.Reference.Primitive.Type.Precision
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class BakerJavaEmitterTest {

    private val emitter = BakerJavaEmitter()

    @Test
    fun emitGetEndpointWithPathParamAndMultipleResponses() {
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

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;

            public interface GetTodoInteraction extends Interaction {
                interface GetTodoOutcome {}
                class GetTodoResponse200 implements GetTodoOutcome {
                    public final TodoDto body;
                    public GetTodoResponse200(TodoDto body) { this.body = body; }
                }
                class GetTodoResponse404 implements GetTodoOutcome {
                    public final ErrorDto body;
                    public GetTodoResponse404(ErrorDto body) { this.body = body; }
                }

                @FiresEvent(oneOf = {GetTodoResponse200.class, GetTodoResponse404.class})
                GetTodoOutcome apply(Long id);
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }

    @Test
    fun emitPostEndpointWithBodyAndMultipleResponses() {
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

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;

            public interface CreateTodoInteraction extends Interaction {
                interface CreateTodoOutcome {}
                class CreateTodoResponse201 implements CreateTodoOutcome {
                    public final TodoDto body;
                    public CreateTodoResponse201(TodoDto body) { this.body = body; }
                }
                class CreateTodoResponse400 implements CreateTodoOutcome {
                    public final ErrorDto body;
                    public CreateTodoResponse400(ErrorDto body) { this.body = body; }
                }

                @FiresEvent(oneOf = {CreateTodoResponse201.class, CreateTodoResponse400.class})
                CreateTodoOutcome apply(CreateTodoRequest body);
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }

    @Test
    fun emitEndpointWithNoBodyResponse() {
        // DELETE /todos/{id} -> { 204 -> (no body), 404 -> ErrorDto }
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
                Endpoint.Response(
                    "204",
                    emptyList(),
                    null,
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

        val result = emitter.emit(endpoint)

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;

            public interface DeleteTodoInteraction extends Interaction {
                interface DeleteTodoOutcome {}
                class DeleteTodoResponse204 implements DeleteTodoOutcome {}
                class DeleteTodoResponse404 implements DeleteTodoOutcome {
                    public final ErrorDto body;
                    public DeleteTodoResponse404(ErrorDto body) { this.body = body; }
                }

                @FiresEvent(oneOf = {DeleteTodoResponse204.class, DeleteTodoResponse404.class})
                DeleteTodoOutcome apply(Long id);
            }
        """.trimIndent()

        assertEquals(expected.trim(), result.trim())
    }
}
