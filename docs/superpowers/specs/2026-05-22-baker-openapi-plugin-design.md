# Baker OpenAPI Plugin Design

## Overview

A new family of modules — `baker-openapi-plugin`, `baker-openapi-emitter`, `baker-openapi-dsl` — that lets Baker users turn an OpenAPI operation into a recipe interaction with minimal ceremony, without coupling the recipe to wirespec-generated response classes.

The goal: replace the four-execution `wirespec-maven-plugin` setup and the response-class-referencing recipe DSL used today (`event<CreateUserInteraction.CreateUserResponse201>()`) with:

```kotlin
recipe("create-current-account") {
    sensoryEvents { event<CreateCurrentAccountEvent>() }

    api(CreateUser) {
        on<CreateUserEndpoint.Response201>(201) fires { resp ->
            UserCreated(id = resp.body.id, email = resp.body.email)
        }
        on<CreateUserEndpoint.Response400>(400) fires { resp ->
            UserCreationFailed(reason = resp.body.message)
        }
    }

    api(CreateProfile) {
        requires(UserCreated::class)
        on<CreateProfileEndpoint.Response201>(201) fires { resp ->
            ProfileCreated(profileId = resp.body.profileId)
        }
    }
}
```

The wirespec response type appears only inside the mapping lambda. The recipe's event graph (`requires(...)`, downstream interactions) is expressed entirely in user-defined domain events.

## Relationship to existing `baker-wirespec`

The existing `core/baker-wirespec` module is an emitter that plugs into `wirespec-maven-plugin` and generates `XxxInteraction` interfaces + `XxxInteractionImpl` implementations per endpoint. Recipes reference the generated response classes directly (e.g. `event<CreateUserInteraction.CreateUserResponse201>()`), which is the coupling this design eliminates.

`baker-wirespec` stays in place for one release. After `baker-openapi-example` is green (see Testing), it is marked `@Deprecated`.

## Module layout

A single parent folder under the root project:

```
baker-openapi/
├── pom.xml                        # aggregator
├── baker-openapi-dsl/             # runtime DSL + generic interaction
├── baker-openapi-emitter/         # wirespec LanguageEmitter (descriptors only)
└── baker-openapi-plugin/          # maven plugin
```

| Module | Purpose | Language | Scope |
|---|---|---|---|
| `baker-openapi-dsl` | Runtime DSL (`api(...) { ... }`, `on(N) fires { ... }`, `requires<E>()`) + generic `ApiOperationInteraction` that builds a Baker `InteractionInstance` from a descriptor + response mappers. Reusable across any operation. | Kotlin | Runtime, consumer dependency |
| `baker-openapi-emitter` | Wirespec `LanguageEmitter` that emits only operation descriptor objects. Models + endpoint classes come from wirespec's standard Kotlin emitter. | Java (matches existing `baker-wirespec` style) | Compile-time, used by the plugin |
| `baker-openapi-plugin` | Maven plugin with a single goal: `generate-from-openapi`. Drives wirespec's OpenAPI converter, then runs the standard Kotlin emitter and the baker-openapi-emitter. | Java | Build-time |

`baker-openapi-plugin` and `baker-openapi-dsl` do not depend on each other. The plugin is build-time only; the DSL is runtime only.

## Generated artifacts (per OpenAPI doc)

The plugin writes into `target/generated-sources/baker-openapi/<package>/`.

### 1. Standard wirespec output (delegated to wirespec's Kotlin emitter)

- `model/UserDto.kt`, `model/ErrorResponse.kt`, … — DTOs for request/response types
- `endpoint/CreateUserEndpoint.kt` — wirespec endpoint class with `Request`, nested `Response201`/`Response400`, `Handler`

### 2. Baker operation descriptors (emitted by `baker-openapi-emitter`)

One file per operation, e.g. `api/CreateUser.kt`:

```kotlin
package com.example.generated.api

object CreateUser : ApiOperation {
    override val operationName = "CreateUser"

    override val inputFields = listOf(
        InputField("firstName",   String::class),
        InputField("lastName",    String::class),
        InputField("email",       String::class),
        InputField("dateOfBirth", String::class),
    )

    override val responseTypes: Map<Int, KClass<*>> = mapOf(
        201 to CreateUserEndpoint.Response201::class,
        400 to CreateUserEndpoint.Response400::class,
    )

    override fun buildRequest(ingredients: Map<String, Any?>): CreateUserEndpoint.Request =
        CreateUserEndpoint.Request(
            UserDto(
                firstName   = ingredients["firstName"]   as String,
                lastName    = ingredients["lastName"]    as String,
                email       = ingredients["email"]       as String,
                dateOfBirth = ingredients["dateOfBirth"] as String,
            )
        )

    override suspend fun invoke(
        handler: Wirespec.Handler,
        request: Any,
    ): Wirespec.Response<*> =
        (handler as CreateUserEndpoint.Handler).createUser(request as CreateUserEndpoint.Request)
}
```

Explicitly **not** generated: no `CreateUserInteraction` interface, no `CreateUserInteractionImpl`. Descriptors are data, not interface scaffolding.

### 3. Nothing else

No per-operation DSL extensions, no scope classes. The DSL is hand-written in `baker-openapi-dsl` and works for any descriptor.

## Runtime DSL (`baker-openapi-dsl`)

### Public surface

```kotlin
@ExperimentalDsl
fun RecipeBuilder.api(
    operation: ApiOperation,
    configure: ApiInteractionScope.() -> Unit,
)

class ApiInteractionScope internal constructor(...) {
    // response mapping — required for every status code the recipe cares about
    fun <R : Any> on(status: Int): ResponseBinding<R>
    infix fun <R : Any> ResponseBinding<R>.fires(mapper: (R) -> Any)

    // optional Baker controls (mirror existing kotlin DSL)
    fun requires(vararg eventClasses: KClass<*>)
    fun maximumInteractionCount(n: Int)
    fun ingredientNameOverrides(block: MutableMap<String, String>.() -> Unit)
}
```

### Internal mechanics of `api(...)`

1. Construct an `ApiOperationInteraction` (a generic Baker `InteractionInstance` implementation) bound to the operation descriptor and the configured status→event mappers.
2. Use the descriptor's `inputFields` to register `IngredientDescriptor`s with Baker — this is how Baker learns the interaction's inputs without an `apply()` method to reflect on.
3. The set of event classes produced by the mappers becomes the interaction's output event set (registered with Baker via `EventDescriptor`s derived from each `KClass`).
4. Apply `requires`, `maximumInteractionCount`, and `ingredientNameOverrides` to the recipe-level interaction binding.

### Generic interaction implementation

```kotlin
class ApiOperationInteraction(
    private val operation: ApiOperation,
    private val handler: Wirespec.Handler,
    private val mappers: Map<Int, (Any) -> Any>,
) : InteractionInstance {
    override val name = operation.operationName
    override val input: List<IngredientDescriptor> = operation.inputFields.map { ... }
    override val output: Map<String, Map<String, Type>> = /* derived from mapper return classes */

    override fun execute(input: List<IngredientInstance>): CompletableFuture<EventInstance?> {
        val ingredients = input.associate { it.name to it.value }
        val request = operation.buildRequest(ingredients)
        val response = runBlocking { operation.invoke(handler, request) }
        val mapper = mappers[response.status]
            ?: error("No mapping for status ${response.status} on ${operation.operationName}")
        val event = mapper(response)
        return CompletableFuture.completedFuture(EventInstance.from(event))
    }
}
```

### Decoupling property

The wirespec response type appears only inside the lambda parameter to `fires { ... }`. The recipe's event graph — `requires(...)`, downstream `api(...) { ... }` blocks, `sensoryEvents { ... }`, the sealed set of events Baker reasons about — uses only user-defined classes. Renaming or replacing the OpenAPI document does not require touching `requires(...)` or any downstream interaction binding; only the mapping lambdas need to be updated.

## Maven plugin (`baker-openapi-plugin`)

### Goal: `generate-from-openapi`

Bound to the `generate-sources` phase by default. One execution per OpenAPI document.

### Consumer pom

```xml
<plugin>
    <groupId>com.ing.baker</groupId>
    <artifactId>baker-openapi-plugin</artifactId>
    <version>${baker.version}</version>
    <executions>
        <execution>
            <id>account-api</id>
            <goals><goal>generate-from-openapi</goal></goals>
            <configuration>
                <input>${project.basedir}/src/main/openapi/account-api.json</input>
                <packageName>com.ing.baker.examples.account.generated</packageName>
            </configuration>
        </execution>
        <execution>
            <id>profile-api</id>
            <goals><goal>generate-from-openapi</goal></goals>
            <configuration>
                <input>${project.basedir}/src/main/openapi/profile-api.json</input>
                <packageName>com.ing.baker.examples.account.generated.profile</packageName>
            </configuration>
        </execution>
    </executions>
</plugin>
```

### Configuration parameters

| Parameter | Default | Notes |
|---|---|---|
| `input` | (required) | Path to OpenAPI v3 file (.json or .yaml) |
| `packageName` | (required) | Target Kotlin package |
| `outputDirectory` | `${project.build.directory}/generated-sources/baker-openapi` | |
| `addToSources` | `true` | Auto-adds output to compile source roots (no `build-helper-maven-plugin` needed) |

### Internal pipeline

1. Read the OpenAPI file and parse it via wirespec's `OpenAPIV3Parser` into a wirespec AST.
2. Run wirespec's standard `KotlinEmitter` over the AST; write `model/*.kt` and `endpoint/*.kt`.
3. Run `BakerOpenApiEmitter` (new) over the AST; write `api/<Operation>.kt` descriptor objects.
4. If `addToSources`, register the output directory as a Maven compile source root via `MavenProject.addCompileSourceRoot(...)`.

### What disappears from the consumer pom

- The four wirespec-maven-plugin executions (Kotlin + Baker, ×2 for OpenAPI + .ws).
- The `<emitterClass>` plumbing.
- The `build-helper-maven-plugin` execution that adds `generated-sources/wirespec` as a source root.

## Runtime wiring

### Consumer runtime dependency

```xml
<dependency>
    <groupId>com.ing.baker</groupId>
    <artifactId>baker-openapi-dsl</artifactId>
    <version>${baker.version}</version>
</dependency>
```

`baker-openapi-dsl` transitively pulls in `baker-recipe-dsl-kotlin`, `baker-interface-kotlin`, and the wirespec runtime (`wirespec-jvm`). Consumers add Jackson + `wirespec-jackson-jvm` themselves — HTTP serialization choice is theirs.

### App startup

```kotlin
val transport = javaHttpTransportation("https://api.example.com")
val serialization = WirespecSerialization(ObjectMapper().registerKotlinModule())

val baker = InMemoryBaker.kotlin(
    implementations = listOf(
        ApiOperationBinding(CreateUser,    transport, serialization),
        ApiOperationBinding(CreateProfile, transport, serialization),
        ApiOperationBinding(CreateAccount, transport, serialization),
    )
)
```

`ApiOperationBinding` is a small factory in `baker-openapi-dsl` that constructs the wirespec `Handler` for an operation (from its descriptor) and pairs it with an `ApiOperationInteraction` instance. The operation list is named once at startup; status→event mappings live in the recipe.

## Module dependency graph

```
baker-openapi-plugin   ──depends──▶  baker-openapi-emitter  ──depends──▶  wirespec-compiler-core-jvm
                                                                          wirespec-openapi-jvm
baker-openapi-dsl      ──depends──▶  baker-recipe-dsl-kotlin
                                     baker-interface-kotlin
                                     wirespec-jvm
```

## Testing

| Target | Approach |
|---|---|
| `baker-openapi-emitter` | Unit: feed wirespec AST fixtures (path params, query, request body, multiple status codes) into the emitter; assert generated `object CreateUser : ApiOperation { ... }` source matches expected. Mirrors the existing `BakerKotlinEmitterTest`. |
| `baker-openapi-dsl` | Unit (DSL): build a recipe with `api(...) { on(201) fires { ... } }`, compile via `RecipeCompiler`, assert the resulting `CompiledRecipe` has the expected ingredients, events, and interactions wired. Unit (runtime): exercise `ApiOperationInteraction.execute(...)` with a fake `Wirespec.Handler` covering matched status, unmatched status (errors), and exception propagation. |
| `baker-openapi-plugin` | Integration: `maven-invoker-plugin` runs `generate-from-openapi` against a fixture OpenAPI file in `src/it/`; assertions on generated file paths and expected substrings. |
| End-to-end | A new `baker-openapi-example` (or migrated `baker-wirespec-example`) runs the WireMock-based recipe test using the new DSL. Proves the whole stack: plugin generates → DSL configures → Baker executes → WireMock responds → events fire. |

## Scope

### In scope (v1)

- `baker-openapi/` aggregator with three child modules.
- OpenAPI v3 JSON input.
- Single OpenAPI document per plugin execution; multiple executions for multiple APIs.
- Kotlin DSL only.
- The `api(operation) { ... }` recipe DSL with `on(N) fires { ... }`, `requires(...)`, `maximumInteractionCount(...)`, `ingredientNameOverrides { ... }`.
- Unit tests for the emitter and DSL; integration test for the plugin; one end-to-end example.

### Out of scope (v1)

- Fallback for unmapped status codes. The runtime errors when a response status has no mapper. A future `onUnmapped { ... }` clause can be added without breaking the DSL.
- `.ws` source input. The plugin handles OpenAPI only. Hand-written wirespec sources are converted to OpenAPI upstream, or a second goal is added later.
- YAML OpenAPI input. Wirespec supports it; allowing `.yaml` in `input` is a follow-up.
- Java DSL. Not generated; not hand-written for v1.
- Custom Maven plugin replacing `wirespec-maven-plugin` for non-Baker projects. This plugin only generates what Baker users need.

## Migration

- New work uses `baker-openapi-plugin` + `baker-openapi-dsl`.
- `baker-wirespec` (existing emitter) stays in place for one release. It is marked `@Deprecated` once `baker-openapi-example` is green.
- The existing `baker-wirespec-example` is either migrated to the new approach (preferable — demonstrates parity) or kept as a frozen reference. Decision deferred to execution time.
