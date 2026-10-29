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

## OpenTelemetry tracing

The in-memory runtime emits spans using OpenTelemetry when built through `InMemoryBaker`.

### What is traced

- Build lifecycle: `baker.build`
- Recipe lifecycle: `baker.recipe-instance.created`
- Event flow: `baker.event.received`, `baker.event.fired`
- Interaction execution: `baker.interaction.<interactionName>`

Interaction spans are created as children of the latest event span for the same recipe instance.

### Common attributes

- `baker.recipe.id`
- `baker.recipe.name`
- `baker.recipe.instance.id`

Depending on the span type, additional attributes are set:

- `baker.event.name`
- `baker.interaction.name`
- `baker.correlation.id`
- `baker.failure.count`
- `error.type` (for failed interactions)

### Injecting a custom tracer

By default, Baker uses `GlobalOpenTelemetry.getTracer(...)`. You can provide your own tracer:

```kotlin
import com.ing.baker.runtime.inmemory.InMemoryBaker
import com.ing.baker.runtime.model.BakerConfig
import io.opentelemetry.api.GlobalOpenTelemetry

val tracer = GlobalOpenTelemetry.getTracer("my-service.baker")
val baker = InMemoryBaker.java(BakerConfig.default(), emptyList(), tracer)
```

For async Java factory usage:

```kotlin
val tracer = GlobalOpenTelemetry.getTracer("my-service.baker")
val bakerFuture = InMemoryBaker.javaAsync(BakerConfig.default(), emptyList(), tracer)
```

