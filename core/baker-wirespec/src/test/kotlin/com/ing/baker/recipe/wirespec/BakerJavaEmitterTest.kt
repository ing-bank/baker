package com.ing.baker.recipe.wirespec

import community.flock.wirespec.compiler.core.parse.ast.*
import community.flock.wirespec.compiler.core.parse.ast.Reference.Primitive.Type.Precision
import community.flock.wirespec.ir.generator.JavaGenerator
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class BakerJavaEmitterTest {

    private val emitter = BakerJavaEmitter()

    private fun render(endpoint: Endpoint): String =
        JavaGenerator.generate(emitter.emit(endpoint)).trim()

    @Test
    fun emitGetEndpointWithPathParamAndMultipleResponses() {
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("GetTodo"),
            method = Endpoint.Method.GET,
            path = listOf(
                Endpoint.Segment.Literal("/todos/"),
                Endpoint.Segment.Param(
                    FieldIdentifier("id"),
                    Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P64, null), false),
                ),
            ),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response("200", emptyList(), Endpoint.Content("application/json", Reference.Custom("TodoDto", false)), emptyList()),
                Endpoint.Response("404", emptyList(), Endpoint.Content("application/json", Reference.Custom("ErrorDto", false)), emptyList()),
            ),
        )

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;
            public interface GetTodoInteraction extends Interaction {
              public interface GetTodoOutcome {
              }
              public static record GetTodoResponse200 (
                TodoDto body
              ) implements GetTodoOutcome {
              };
              public static record GetTodoResponse404 (
                ErrorDto body
              ) implements GetTodoOutcome {
              };
              @FiresEvent(oneOf = {GetTodoResponse200.class, GetTodoResponse404.class})  public GetTodoOutcome apply(Long id);
            }
        """.trimIndent().trim()

        assertEquals(expected, render(endpoint))
    }

    @Test
    fun emitPostEndpointWithBodyAndMultipleResponses() {
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
                    Endpoint.Content("application/json", Reference.Custom("CreateTodoRequest", false)),
                ),
            ),
            responses = listOf(
                Endpoint.Response("201", emptyList(), Endpoint.Content("application/json", Reference.Custom("TodoDto", false)), emptyList()),
                Endpoint.Response("400", emptyList(), Endpoint.Content("application/json", Reference.Custom("ErrorDto", false)), emptyList()),
            ),
        )

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;
            public interface CreateTodoInteraction extends Interaction {
              public interface CreateTodoOutcome {
              }
              public static record CreateTodoResponse201 (
                TodoDto body
              ) implements CreateTodoOutcome {
              };
              public static record CreateTodoResponse400 (
                ErrorDto body
              ) implements CreateTodoOutcome {
              };
              @FiresEvent(oneOf = {CreateTodoResponse201.class, CreateTodoResponse400.class})  public CreateTodoOutcome apply(CreateTodoRequest body);
            }
        """.trimIndent().trim()

        assertEquals(expected, render(endpoint))
    }

    @Test
    fun emitEndpointWithNoBodyResponse() {
        val endpoint = Endpoint(
            comment = null,
            annotations = emptyList(),
            identifier = DefinitionIdentifier("DeleteTodo"),
            method = Endpoint.Method.DELETE,
            path = listOf(
                Endpoint.Segment.Literal("/todos/"),
                Endpoint.Segment.Param(
                    FieldIdentifier("id"),
                    Reference.Primitive(Reference.Primitive.Type.Integer(Precision.P64, null), false),
                ),
            ),
            queries = emptyList(),
            headers = emptyList(),
            requests = listOf(Endpoint.Request(null)),
            responses = listOf(
                Endpoint.Response("204", emptyList(), null, emptyList()),
                Endpoint.Response("404", emptyList(), Endpoint.Content("application/json", Reference.Custom("ErrorDto", false)), emptyList()),
            ),
        )

        val expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;
            public interface DeleteTodoInteraction extends Interaction {
              public interface DeleteTodoOutcome {
              }
              public static record DeleteTodoResponse204 () implements DeleteTodoOutcome {
              };
              public static record DeleteTodoResponse404 (
                ErrorDto body
              ) implements DeleteTodoOutcome {
              };
              @FiresEvent(oneOf = {DeleteTodoResponse204.class, DeleteTodoResponse404.class})  public DeleteTodoOutcome apply(Long id);
            }
        """.trimIndent().trim()

        assertEquals(expected, render(endpoint))
    }
}
