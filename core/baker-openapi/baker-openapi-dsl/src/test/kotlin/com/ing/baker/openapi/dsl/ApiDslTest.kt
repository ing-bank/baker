package com.ing.baker.openapi.dsl

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import kotlin.reflect.KClass
import scala.jdk.javaapi.CollectionConverters

private data class DslSensoryEvent(val firstName: String, val email: String)
private data class DslUserCreated(val id: String, val email: String)
private data class DslUserCreationFailed(val reason: String)

private class DslFakeHandler : Wirespec.Handler
private object DslFakeHeaders : Wirespec.Response.Headers
private class DslFakeResponse(override val status: Int) : Wirespec.Response<Unit> {
    override val body: Unit = Unit
    override val headers: Wirespec.Response.Headers = DslFakeHeaders
}

private object CreateUser : ApiOperation {
    override val operationName = "CreateUser"
    override val inputFields = listOf(
        InputField("firstName", String::class),
        InputField("email", String::class),
    )
    override val responseTypes: Map<Int, KClass<*>> = mapOf(
        201 to DslFakeResponse::class,
        400 to DslFakeResponse::class,
    )
    override val handlerClass = DslFakeHandler::class
    override fun buildRequest(ingredients: Map<String, Any?>): Any = ingredients
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> =
        DslFakeResponse(201)
    override fun buildHandler(
        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,
        serialization: Wirespec.Serialization,
    ): Wirespec.Handler = DslFakeHandler()
}

@OptIn(ExperimentalDsl::class)
class ApiDslTest {

    @Test
    fun `api block registers an interaction with the operation name and inputs`() {
        val r = recipe("r") {
            sensoryEvents { event<DslSensoryEvent>() }
            api(CreateUser) {
                on<DslFakeResponse, DslUserCreated>(201) { DslUserCreated("u1", "a@b") }
                on<DslFakeResponse, DslUserCreationFailed>(400) { DslUserCreationFailed("nope") }
            }
        }
        val compiled = RecipeCompiler.compileRecipe(r)
        val interaction = CollectionConverters.asJava(compiled.interactionTransitions())
            .single { it.interactionName() == "CreateUser" }
        val ingredientNames = CollectionConverters.asJava(interaction.requiredIngredients())
            .map { it.name() }
            .toSet()
        assertEquals(setOf("firstName", "email"), ingredientNames)
    }

    @Test
    fun `api block exposes user-mapped events as interaction outputs`() {
        val r = recipe("r") {
            sensoryEvents { event<DslSensoryEvent>() }
            api(CreateUser) {
                on<DslFakeResponse, DslUserCreated>(201) { DslUserCreated("u1", "a@b") }
                on<DslFakeResponse, DslUserCreationFailed>(400) { DslUserCreationFailed("nope") }
            }
        }
        val compiled = RecipeCompiler.compileRecipe(r)
        val outputs = CollectionConverters.asJava(compiled.events())
            .map { it.name() }
            .toSet()
        assertTrue(outputs.contains("DslUserCreated"), "outputs were: $outputs")
        assertTrue(outputs.contains("DslUserCreationFailed"), "outputs were: $outputs")
    }

    @Test
    fun `requires registers required events on the DSL interaction`() {
        val r = recipe("r") {
            sensoryEvents { event<DslSensoryEvent>() }
            api(CreateUser) {
                requires(DslUserCreated::class)
                on<DslFakeResponse, DslUserCreated>(201) { DslUserCreated("u1", "a@b") }
            }
        }
        val interaction = CollectionConverters.asJava(r.interactions())
            .single { it.name() == "CreateUser" }
        val reqEvents = CollectionConverters.asJava(interaction.requiredEvents())
        assertTrue(reqEvents.contains("DslUserCreated"), "got: $reqEvents")
    }
}
