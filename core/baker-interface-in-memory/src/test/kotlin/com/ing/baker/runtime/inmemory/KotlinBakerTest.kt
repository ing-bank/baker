package com.ing.baker.runtime.inmemory

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipeJava
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.javadsl.EventInstance
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.lang.reflect.Method
import java.util.UUID
import kotlin.time.Duration.Companion.seconds

class KotlinBakerTest {

    @Test
    fun `fire event and await completion exposes state and ingredients`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeA")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)

                val received = baker.fireSensoryEventAndAwaitReceived(
                    recipeInstanceId,
                    EventInstance.from(TestRecipeJava.InitialEvent("value-a"))
                )
                val completed = baker.awaitCompleted(recipeInstanceId, 2.seconds)
                val ingredient = baker.getIngredient(recipeInstanceId, "initialIngredient").`as`(String::class.java)
                val eventNames = baker.getEventNames(recipeInstanceId)

                assertEquals(SensoryEventStatus.Received, received)
                assertEquals(SensoryEventStatus.Completed, completed)
                assertEquals("value-a", ingredient)
                assertTrue(eventNames.contains("InitialEvent"))
                assertTrue(baker.hasRecipeInstance(recipeInstanceId))
            }
        }
    }

    @Test
    fun `awaitEvent resolves when event already happened`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeB")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)
                baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(TestRecipeJava.InitialEvent("value-b")))

                baker.awaitEvent(recipeInstanceId, "InitialEvent", 1.seconds)

                val eventNames = baker.getEventNames(recipeInstanceId)
                assertTrue(eventNames.contains("InitialEvent"))
            }
        }
    }

    @Test
    fun `bake with metadata overload executes successfully`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeC")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId, mapOf("key" to "value"))
                baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, EventInstance.from(TestRecipeJava.InitialEvent("value-c")))
                val status = baker.awaitCompleted(recipeInstanceId, 2.seconds)

                assertEquals(SensoryEventStatus.Completed, status)
                assertTrue(baker.hasRecipeInstance(recipeInstanceId))
            }
        }
    }

    @Test
    fun `deprecated fireEvent resolutions complete with expected statuses`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeD")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)
                val resolutions = baker.fireEvent(recipeInstanceId, EventInstance.from(TestRecipeJava.InitialEvent("value-d")))

                val (received, completed) = awaitAll(
                    async { resolutions.resolveWhenReceived.await() },
                    async { resolutions.resolveWhenCompleted.await().sensoryEventStatus }
                )

                assertEquals(SensoryEventStatus.Received, received)
                assertEquals(SensoryEventStatus.Completed, completed)
            }
        }
    }

    @Test
    fun `deprecated fireEventAndResolveWhenReceived returns Received`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeE")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)
                val status = baker.fireEventAndResolveWhenReceived(
                    recipeInstanceId,
                    EventInstance.from(TestRecipeJava.InitialEvent("value-e"))
                )

                assertEquals(SensoryEventStatus.Received, status)
            }
        }
    }

    @Test
    fun `deprecated fireEventAndResolveWhenCompleted returns Completed`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeF")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)
                val result = baker.fireEventAndResolveWhenCompleted(
                    recipeInstanceId,
                    EventInstance.from(TestRecipeJava.InitialEvent("value-f"))
                )

                assertEquals(SensoryEventStatus.Completed, result.sensoryEventStatus)
                assertTrue(result.eventNames.contains("InitialEvent"))
            }
        }
    }

    @Test
    fun `deprecated fireEventAndResolveOnEvent resolves when target event occurs`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(simpleRecipe("KotlinAdapterRecipeG")), validate = false)
                val recipeInstanceId = UUID.randomUUID().toString()

                baker.bake(recipeId, recipeInstanceId)
                val result = baker.fireEventAndResolveOnEvent(
                    recipeInstanceId,
                    EventInstance.from(TestRecipeJava.InitialEvent("value-g")),
                    "InitialEvent"
                )

                assertEquals(SensoryEventStatus.Completed, result.sensoryEventStatus)
                assertTrue(result.eventNames.contains("InitialEvent"))
            }
        }
    }

    @Test
    fun `awaitCompleted throws for unknown process`() {
        runBlocking {
            KotlinBaker.java().use { baker ->
                val unknown = UUID.randomUUID().toString()
                org.junit.jupiter.api.Assertions.assertThrows(NoSuchProcessException::class.java) {
                    runBlocking {
                        withTimeout(2.seconds) {
                            baker.awaitCompleted(unknown, 1.seconds)
                        }
                    }
                }
            }
        }
    }

    @Test
    fun `mirrors common baker method names`() {
        val expected = publicMethodNames(com.ing.baker.runtime.common.Baker::class.java)
        val actual = publicMethodNames(KotlinBaker::class.java)

        val missing = expected.minus(actual)
        assertTrue(missing.isEmpty(), "Missing methods in in-memory KotlinBaker: $missing")
    }

    @Test
    fun `exposes async bridge entry points`() {
        val methodNames = publicMethodNames(KotlinBaker::class.java)

        assertTrue(methodNames.any { it.startsWith("addRecipeAsync") })
        assertTrue(methodNames.any { it.startsWith("bakeAsync") })
        assertTrue(methodNames.any { it.startsWith("gracefulShutdownAsync") })
        assertTrue(methodNames.any { it.startsWith("fireSensoryEventAndAwaitReceivedAsync") })
        assertTrue(methodNames.any { it.startsWith("awaitCompletedAsync") })
    }

    private fun simpleRecipe(name: String): Recipe =
        Recipe(name).withSensoryEvent(TestRecipeJava.InitialEvent::class.java)

    private fun publicMethodNames(clazz: Class<*>): Set<String> =
        clazz.declaredMethods
            .filter { method ->
                java.lang.reflect.Modifier.isPublic(method.modifiers) &&
                    !method.isSynthetic &&
                    !method.name.contains($$"$annotations") &&
                    !method.name.startsWith($$"access$")
            }
            .map { it.sanitizedName() }
            .filterNot { it == "toNullable" || it == $$"$init$" }
            .toSet()

    // Kotlin default arguments create JVM methods named foo$default. We normalize those names.
    private fun Method.sanitizedName(): String =
        name
            .substringBefore($$"$default")
            // Kotlin value classes (for example kotlin.time.Duration) mangle method names as foo-xxxx.
            .substringBefore("-")
}

