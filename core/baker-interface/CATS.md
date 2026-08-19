# Can we implement `Baker[F[_]]` in Kotlin with coroutines and no Cats dependency?

If you are changing code in `core/baker-interface/src/main/scala/com/ing/baker/runtime/model`, see `core/baker-interface/EFFECT-ABSTRACTION.md` for the local effect-abstraction contract.

Yes — with one important constraint: **not directly as `suspend` methods**.

### Quick answer
`Baker[F[_]]` is a Scala higher-kinded interface (`F[_]`). Kotlin cannot express higher-kinded types, and `suspend` is not a JVM type you can plug into `F[_]`.  
So a Kotlin class cannot cleanly “implement `Baker[F[_]]` with coroutines” in a native way.

### What you can do instead (no Cats dependency)

- Implement the **Java-facing Baker API** from this project (the one likely using `CompletionStage`/`CompletableFuture`) rather than the Scala HKT trait in `core/baker-interface/.../Baker.scala`.
- In Kotlin, keep your internals as `suspend` functions.
- Bridge:
    - `suspend -> CompletableFuture` for API methods (using `kotlinx-coroutines-jdk8` `future { ... }`)
    - `CompletableFuture -> suspend` when calling Java async APIs (`await()` from `kotlinx-coroutines-jdk8`)
- This gives coroutine ergonomics **without Cats Effect dependency**.

### Why this is the right boundary
From your `Baker.scala`, methods are all shaped like `def x(...): F[...]`. That abstraction is designed for Scala effect types (e.g., `IO`, `Future`). Kotlin interop with such HKT-heavy traits is awkward/impractical.  
The stable interop boundary on JVM is usually Java async types (`CompletionStage`) or blocking types.

### Practical architecture
1. Keep Scala `Baker[F[_]]` as-is for Scala users.
2. Expose/use a Java/Kotlin-friendly interface (`CompletionStage`).
3. Add a Kotlin adapter layer with `suspend` API if you want idiomatic coroutine call sites.

Example shape:

```kotlin
interface KotlinBaker {
    suspend fun bake(recipeId: String, recipeInstanceId: String)
    suspend fun fireSensoryEventAndAwaitReceived(
        recipeInstanceId: String,
        event: EventInstance
    ): SensoryEventStatus
}
```

And adapter to Java Baker:

```kotlin
class KotlinBakerImpl(
    private val delegate: JavaBaker, // e.g., methods return CompletionStage<T>
    private val scope: CoroutineScope
) : KotlinBaker {

    override suspend fun bake(recipeId: String, recipeInstanceId: String) {
        delegate.bake(recipeId, recipeInstanceId).await()
    }

    fun bakeAsync(recipeId: String, recipeInstanceId: String): CompletableFuture<Unit> =
        scope.future { bake(recipeId, recipeInstanceId) }
}
```

### Bottom line
- **Directly implementing `Baker[F[_]]` in Kotlin with `suspend` as `F`**: no.
- **Using Kotlin coroutines with Baker and zero Cats dependency**: yes, via Java async interface + adapters.

If you want, I can help map your exact Baker module interfaces (`Scala`, `Java`, `Kotlin`) and suggest the cleanest adapter location in this repo structure.