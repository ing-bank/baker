# KotlinBaker (in-memory)

`com.ing.baker.runtime.inmemory.KotlinBaker` is a coroutine-friendly adapter around the Java in-memory Baker API.
It keeps a `CompletableFuture` boundary while exposing `suspend` methods for Kotlin callers.

## Quick usage

```kotlin
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipeJava
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.runtime.inmemory.KotlinBaker
import com.ing.baker.runtime.javadsl.EventInstance
import kotlinx.coroutines.runBlocking
import kotlin.time.Duration.Companion.seconds

fun main() = runBlocking {
    KotlinBaker.java().use { baker ->
        val recipe = Recipe("ExampleRecipe")
            .withSensoryEvent(TestRecipeJava.InitialEvent::class.java)

        val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(recipe), validate = false)
        val recipeInstanceId = "instance-1"

        baker.bake(recipeId, recipeInstanceId)
        baker.fireSensoryEventAndAwaitReceived(
            recipeInstanceId,
            EventInstance.from(TestRecipeJava.InitialEvent("hello"))
        )
        baker.awaitCompleted(recipeInstanceId, 5.seconds)
    }
}
```

## Notes

- `KotlinBaker` mirrors the Kotlin adapter shape from `baker-interface-kotlin`.
- It supports `suspend` APIs and selected `CompletableFuture` wrappers such as `javaAsync`, `bakeAsync`, and `awaitCompletedAsync`.

