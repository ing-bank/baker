# Baker OpenAPI Plugin Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `baker-openapi/` aggregator with three modules — `baker-openapi-dsl` (runtime), `baker-openapi-emitter` (codegen), `baker-openapi-plugin` (Maven plugin) — so users turn OpenAPI operations into recipe interactions via `api(Operation) { on(N) fires { ... } }`, without referencing wirespec-generated response classes in the recipe.

**Architecture:** The plugin parses OpenAPI → wirespec AST, runs wirespec's standard Kotlin emitter for models + endpoint classes, and runs a custom emitter that writes one `object` per operation implementing `ApiOperation`. At runtime, the `api(Operation) { ... }` DSL constructs a generic `ApiOperationInteraction` (implements `InteractionInstance`) bound to the descriptor plus user response mappers, and registers a matching `Interaction` in the recipe via the existing kotlin-DSL machinery.

**Tech Stack:** Kotlin 1.9+ (DSL), Java 17 (emitter, plugin), Maven, JUnit 5, wirespec 0.17.20 (`wirespec-compiler-core-jvm`, `wirespec-openapi-jvm`), Baker 5.1.0-SNAPSHOT (`baker-recipe-dsl-kotlin`, `baker-interface-kotlin`).

**Spec:** `docs/superpowers/specs/2026-05-22-baker-openapi-plugin-design.md`

---

## File Structure

Every new file is created under `baker-openapi/` at repo root.

```
baker-openapi/
├── pom.xml                                                        # Task 1 — aggregator
│
├── baker-openapi-dsl/
│   ├── pom.xml                                                    # Task 2
│   └── src/
│       ├── main/kotlin/com/ing/baker/openapi/dsl/
│       │   ├── ApiOperation.kt                                    # Task 3 — interfaces + InputField
│       │   ├── ApiOperationInteraction.kt                         # Task 4 — generic InteractionInstance
│       │   ├── ApiDsl.kt                                          # Task 5 — RecipeBuilder.api + scope
│       │   └── ApiOperationBinding.kt                             # Task 6 — runtime factory
│       └── test/kotlin/com/ing/baker/openapi/dsl/
│           ├── ApiOperationInteractionTest.kt                     # Task 4
│           ├── ApiDslTest.kt                                      # Task 5
│           └── ApiOperationBindingTest.kt                         # Task 6
│
├── baker-openapi-emitter/
│   ├── pom.xml                                                    # Task 7
│   └── src/
│       ├── main/java/com/ing/baker/openapi/emitter/
│       │   └── BakerOpenApiEmitter.java                           # Task 8
│       └── test/kotlin/com/ing/baker/openapi/emitter/
│           └── BakerOpenApiEmitterTest.kt                         # Task 8
│
├── baker-openapi-plugin/
│   ├── pom.xml                                                    # Task 9
│   └── src/
│       ├── main/java/com/ing/baker/openapi/plugin/
│       │   └── GenerateFromOpenApiMojo.java                       # Task 10
│       └── it/
│           ├── settings.xml                                       # Task 10
│           └── happy-path/
│               ├── pom.xml                                        # Task 10
│               ├── src/main/openapi/petstore.json                 # Task 10
│               └── verify.groovy                                  # Task 10
│
└── (root pom modified — Task 1)
```

End-to-end example (`examples/baker-openapi-example/`) is built in Task 11 — module skeleton, OpenAPI fixture, recipe, WireMock test.

A small upstream change to `baker-recipe-dsl-kotlin/src/main/kotlin/com/ing/baker/recipe/kotlindsl/KotlinDsl.kt` is made in Task 5 to expose an `addInteraction(Interaction)` method we can call from a non-inline extension.

---

## Task 1: Aggregator pom + root registration

**Files:**
- Create: `baker-openapi/pom.xml`
- Modify: `pom.xml` (root, lines around 129 where `core/baker-wirespec` is listed)

- [ ] **Step 1: Create the aggregator pom**

Write `baker-openapi/pom.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
         xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
    <modelVersion>4.0.0</modelVersion>

    <parent>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker</artifactId>
        <version>5.1.0-SNAPSHOT</version>
        <relativePath>../pom.xml</relativePath>
    </parent>

    <artifactId>baker-openapi</artifactId>
    <name>Baker OpenAPI (aggregator)</name>
    <packaging>pom</packaging>

    <properties>
        <wirespec.version>0.17.20</wirespec.version>
    </properties>

    <modules>
        <module>baker-openapi-dsl</module>
        <module>baker-openapi-emitter</module>
        <module>baker-openapi-plugin</module>
    </modules>
</project>
```

- [ ] **Step 2: Register the aggregator in the root pom**

Open root `pom.xml`, find the `<module>core/baker-wirespec</module>` line (~line 129) and add the new aggregator immediately after it:

```xml
        <module>core/baker-wirespec</module>
        <module>baker-openapi</module>
```

- [ ] **Step 3: Verify the aggregator resolves**

Run: `mvn -pl baker-openapi -N help:effective-pom -q | tail -20`
Expected: prints the effective pom for `baker-openapi` without errors. Three child modules listed but not yet present, so a follow-up build will fail — that's expected; we add them next.

- [ ] **Step 4: Commit**

```bash
git add baker-openapi/pom.xml pom.xml
git commit -m "feat: add baker-openapi aggregator module"
```

---

## Task 2: baker-openapi-dsl module skeleton

**Files:**
- Create: `baker-openapi/baker-openapi-dsl/pom.xml`
- Create: `baker-openapi/baker-openapi-dsl/src/main/kotlin/.gitkeep`
- Create: `baker-openapi/baker-openapi-dsl/src/test/kotlin/.gitkeep`

- [ ] **Step 1: Create the dsl pom**

Write `baker-openapi/baker-openapi-dsl/pom.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
         xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
    <modelVersion>4.0.0</modelVersion>

    <parent>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker-openapi</artifactId>
        <version>5.1.0-SNAPSHOT</version>
        <relativePath>../pom.xml</relativePath>
    </parent>

    <artifactId>baker-openapi-dsl</artifactId>
    <name>Baker OpenAPI DSL</name>
    <description>Runtime DSL for building Baker recipes from generated OpenAPI operation descriptors</description>

    <dependencies>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-recipe-dsl-kotlin</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-interface-kotlin</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-compiler</artifactId>
            <version>${project.version}</version>
            <scope>test</scope>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-stdlib</artifactId>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-reflect</artifactId>
            <version>${kotlin.version}</version>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlinx</groupId>
            <artifactId>kotlinx-coroutines-core</artifactId>
        </dependency>
        <dependency>
            <groupId>community.flock.wirespec.integration</groupId>
            <artifactId>wirespec-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>

        <dependency>
            <groupId>org.junit.jupiter</groupId>
            <artifactId>junit-jupiter-engine</artifactId>
            <scope>test</scope>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-test-junit5</artifactId>
            <version>${kotlin.version}</version>
            <scope>test</scope>
        </dependency>
    </dependencies>

    <build>
        <sourceDirectory>src/main/kotlin</sourceDirectory>
        <testSourceDirectory>src/test/kotlin</testSourceDirectory>
        <plugins>
            <plugin>
                <groupId>org.jetbrains.kotlin</groupId>
                <artifactId>kotlin-maven-plugin</artifactId>
                <version>${kotlin.version}</version>
                <configuration>
                    <jvmTarget>${jvm.target}</jvmTarget>
                </configuration>
                <executions>
                    <execution>
                        <id>compile</id>
                        <phase>process-sources</phase>
                        <goals><goal>compile</goal></goals>
                    </execution>
                    <execution>
                        <id>test-compile</id>
                        <phase>process-test-sources</phase>
                        <goals><goal>test-compile</goal></goals>
                    </execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-surefire-plugin</artifactId>
                <configuration>
                    <skipTests>false</skipTests>
                </configuration>
            </plugin>
        </plugins>
    </build>
</project>
```

- [ ] **Step 2: Create empty source dirs**

```bash
mkdir -p baker-openapi/baker-openapi-dsl/src/main/kotlin
mkdir -p baker-openapi/baker-openapi-dsl/src/test/kotlin
touch baker-openapi/baker-openapi-dsl/src/main/kotlin/.gitkeep
touch baker-openapi/baker-openapi-dsl/src/test/kotlin/.gitkeep
```

- [ ] **Step 3: Verify build**

Run: `mvn -pl baker-openapi/baker-openapi-dsl -am compile -q`
Expected: `BUILD SUCCESS` — no Kotlin sources yet, but the module compiles.

- [ ] **Step 4: Commit**

```bash
git add baker-openapi/baker-openapi-dsl
git commit -m "feat: add baker-openapi-dsl module skeleton"
```

---

## Task 3: Define `ApiOperation` and `InputField`

These are the contract types the generated descriptor objects implement. No tests in this task — they're pure interfaces validated by usage in later tasks.

**Files:**
- Create: `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperation.kt`

- [ ] **Step 1: Write the interface file**

Write `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperation.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import community.flock.wirespec.kotlin.Wirespec
import kotlin.reflect.KClass

/**
 * A single input ingredient an API operation expects (from path, query, headers, or
 * flattened request body fields). The runtime DSL turns each entry into a Baker
 * ingredient with the same name.
 */
data class InputField(
    val name: String,
    val type: KClass<*>,
)

/**
 * Descriptor for one OpenAPI operation. Implementations are generated by the plugin —
 * one `object` per operation — and are pure data plus three callbacks the runtime
 * uses to build requests and invoke the wirespec handler.
 */
interface ApiOperation {
    /** Stable name for this operation. Used as the Baker interaction name. */
    val operationName: String

    /** Input ingredients in declaration order. */
    val inputFields: List<InputField>

    /** Maps HTTP status codes to the wirespec response class for that status. */
    val responseTypes: Map<Int, KClass<*>>

    /** Builds the wirespec Request from a name → value ingredient map. */
    fun buildRequest(ingredients: Map<String, Any?>): Any

    /** Invokes the underlying wirespec handler. The handler must be of the operation's expected type. */
    suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*>

    /** The wirespec handler class this operation expects. The plugin generates this. */
    val handlerClass: KClass<out Wirespec.Handler>
}
```

- [ ] **Step 2: Verify it compiles**

Run: `mvn -pl baker-openapi/baker-openapi-dsl -am compile -q`
Expected: `BUILD SUCCESS`.

- [ ] **Step 3: Commit**

```bash
git add baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperation.kt
git commit -m "feat: add ApiOperation and InputField contract types"
```

---

## Task 4: `ApiOperationInteraction` — the generic `InteractionInstance`

**Files:**
- Create: `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteraction.kt`
- Create: `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteractionTest.kt`

- [ ] **Step 1: Write the failing tests**

Write `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteractionTest.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.types.PrimitiveValue
import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import kotlin.reflect.KClass

// A minimal fake handler so the test isn't coupled to a generated endpoint class.
private class FakeHandler : Wirespec.Handler

private class FakeResponse(override val status: Int, val body: Map<String, Any?>) : Wirespec.Response<Map<String, Any?>> {
    override val headers: Map<String, List<String>> = emptyMap()
    override fun getBody(): Map<String, Any?> = body
}

private data class UserCreated(val id: String, val email: String)
private data class UserCreationFailed(val reason: String)

private class FakeOperation(
    private val nextResponse: Wirespec.Response<*>,
) : ApiOperation {
    override val operationName: String = "CreateUser"
    override val inputFields = listOf(
        InputField("firstName", String::class),
        InputField("email", String::class),
    )
    override val responseTypes: Map<Int, KClass<*>> = mapOf(
        201 to FakeResponse::class,
        400 to FakeResponse::class,
    )
    override val handlerClass: KClass<out Wirespec.Handler> = FakeHandler::class
    var capturedRequest: Map<String, Any?>? = null
    override fun buildRequest(ingredients: Map<String, Any?>): Any {
        capturedRequest = ingredients
        return ingredients
    }
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> = nextResponse
}

class ApiOperationInteractionTest {

    @Test
    fun `name returns operationName`() {
        val op = FakeOperation(FakeResponse(201, emptyMap()))
        val interaction = ApiOperationInteraction(op, FakeHandler(), emptyMap())
        assertEquals("CreateUser", interaction.name())
    }

    @Test
    fun `input returns one InteractionInstanceInput per input field`() {
        val op = FakeOperation(FakeResponse(201, emptyMap()))
        val interaction = ApiOperationInteraction(op, FakeHandler(), emptyMap())
        val inputs = interaction.input()
        assertEquals(2, inputs.size)
        assertEquals("firstName", inputs[0].name.orElseThrow())
        assertEquals("email", inputs[1].name.orElseThrow())
    }

    @Test
    fun `execute routes 201 through the configured mapper and returns the fired event`() {
        val op = FakeOperation(FakeResponse(201, emptyMap()))
        val mapper: (Wirespec.Response<*>) -> Any = { resp ->
            val body = (resp as FakeResponse).body
            UserCreated(id = body["id"] as String, email = body["email"] as String)
        }
        // Use a response that carries the data the mapper expects.
        val op2 = FakeOperation(FakeResponse(201, mapOf("id" to "u1", "email" to "a@b")))
        val interaction = ApiOperationInteraction(op2, FakeHandler(), mapOf(201 to mapper))

        val event = interaction.execute(
            mutableListOf(
                IngredientInstance("firstName", PrimitiveValue("John")),
                IngredientInstance("email", PrimitiveValue("a@b")),
            ),
            scala.collection.immutable.Map.empty()
        ).get()

        assertTrue(event.isPresent)
        assertEquals("UserCreated", event.get().name)
        // buildRequest received the ingredients
        assertEquals(mapOf("firstName" to "John", "email" to "a@b"), op2.capturedRequest)
    }

    @Test
    fun `execute throws on unmapped status`() {
        val op = FakeOperation(FakeResponse(500, emptyMap()))
        val interaction = ApiOperationInteraction(op, FakeHandler(), mapOf(201 to { _ -> UserCreated("x", "y") }))

        val ex = assertThrows<java.util.concurrent.ExecutionException> {
            interaction.execute(
                mutableListOf(
                    IngredientInstance("firstName", PrimitiveValue("John")),
                    IngredientInstance("email", PrimitiveValue("a@b")),
                ),
                scala.collection.immutable.Map.empty()
            ).get()
        }
        assertNotNull(ex.cause)
        assertTrue(ex.cause!!.message!!.contains("500"))
        assertTrue(ex.cause!!.message!!.contains("CreateUser"))
    }
}
```

- [ ] **Step 2: Run tests, confirm they fail**

Run: `mvn -pl baker-openapi/baker-openapi-dsl test -q`
Expected: compilation error — `ApiOperationInteraction` does not exist.

- [ ] **Step 3: Implement `ApiOperationInteraction`**

Write `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteraction.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.javadsl.InteractionInstanceInput
import com.ing.baker.types.Converters
import community.flock.wirespec.kotlin.Wirespec
import kotlinx.coroutines.runBlocking
import scala.collection.immutable.Map
import java.util.Optional
import java.util.concurrent.CompletableFuture

typealias ResponseMapper = (Wirespec.Response<*>) -> Any

class ApiOperationInteraction(
    private val operation: ApiOperation,
    private val handler: Wirespec.Handler,
    private val mappers: kotlin.collections.Map<Int, ResponseMapper>,
) : InteractionInstance() {

    override fun name(): String = operation.operationName

    override fun input(): List<InteractionInstanceInput> =
        operation.inputFields.map { field ->
            InteractionInstanceInput(
                Optional.of(field.name),
                Converters.readJavaType(field.type.java),
            )
        }

    override fun execute(
        input: MutableList<IngredientInstance>,
        metadata: Map<String, String>,
    ): CompletableFuture<Optional<EventInstance>> = run(input)

    override fun execute(input: Any, metaData: Map<String, String>): CompletableFuture<Optional<EventInstance>> {
        throw UnsupportedOperationException("ApiOperationInteraction does not support single-input execute()")
    }

    override fun run(input: MutableList<IngredientInstance>): CompletableFuture<Optional<EventInstance>> {
        return try {
            val ingredientMap = input.associate { it.name to it.value.`as`(operation.inputFieldType(it.name)) }
            val request = operation.buildRequest(ingredientMap)
            val response = runBlocking { operation.invoke(handler, request) }
            val mapper = mappers[response.status]
                ?: error("No mapping configured for status ${response.status} on operation ${operation.operationName}")
            val event = mapper(response)
            CompletableFuture.completedFuture(Optional.ofNullable(EventInstance.from(event)))
        } catch (e: Exception) {
            CompletableFuture.failedFuture(e)
        }
    }
}

private fun ApiOperation.inputFieldType(name: String): java.lang.reflect.Type =
    inputFields.first { it.name == name }.type.java
```

- [ ] **Step 4: Run tests, confirm pass**

Run: `mvn -pl baker-openapi/baker-openapi-dsl test -q`
Expected: `Tests run: 4, Failures: 0, Errors: 0`.

- [ ] **Step 5: Commit**

```bash
git add baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteraction.kt \
        baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationInteractionTest.kt
git commit -m "feat: add ApiOperationInteraction routing by status code"
```

---

## Task 5: `api(...)` DSL — `RecipeBuilder` extension + `ApiInteractionScope`

The DSL needs to add an `Interaction` directly to the `RecipeBuilder`'s interactions set. That field is `@PublishedApi internal`. We add a public `addInteraction(Interaction)` method in `baker-recipe-dsl-kotlin` to avoid forcing the api(...) function to be inline.

**Files:**
- Modify: `core/baker-recipe-dsl-kotlin/src/main/kotlin/com/ing/baker/recipe/kotlindsl/KotlinDsl.kt` (after line 99, the existing `interaction<T>(...)` definition)
- Create: `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiDsl.kt`
- Create: `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiDslTest.kt`

- [ ] **Step 1: Write the failing tests**

Write `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiDslTest.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import kotlin.reflect.KClass

private data class SensoryEvent(val firstName: String, val email: String)
private data class UserCreated(val id: String, val email: String)
private data class UserCreationFailed(val reason: String)

private class FakeHandler : Wirespec.Handler
private class FakeResponse(override val status: Int) : Wirespec.Response<Unit> {
    override val headers: Map<String, List<String>> = emptyMap()
    override fun getBody(): Unit = Unit
}

private object CreateUser : ApiOperation {
    override val operationName = "CreateUser"
    override val inputFields = listOf(InputField("firstName", String::class), InputField("email", String::class))
    override val responseTypes: Map<Int, KClass<*>> = mapOf(201 to FakeResponse::class, 400 to FakeResponse::class)
    override val handlerClass = FakeHandler::class
    override fun buildRequest(ingredients: Map<String, Any?>): Any = ingredients
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> = FakeResponse(201)
}

@OptIn(ExperimentalDsl::class)
class ApiDslTest {

    @Test
    fun `api block registers an interaction with the operation name and inputs`() {
        val r = recipe("r") {
            sensoryEvents { event<SensoryEvent>() }
            api(CreateUser) {
                on<FakeResponse>(201) fires { UserCreated("u1", "a@b") }
                on<FakeResponse>(400) fires { UserCreationFailed("nope") }
            }
        }
        val compiled = RecipeCompiler.compileRecipe(r)
        val interaction = compiled.interactionTransitions.single { it.interactionName == "CreateUser" }
        val ingredientNames = interaction.requiredIngredients.map { it.name() }.toSet()
        assertEquals(setOf("firstName", "email"), ingredientNames)
    }

    @Test
    fun `api block exposes user-mapped events as interaction outputs`() {
        val r = recipe("r") {
            sensoryEvents { event<SensoryEvent>() }
            api(CreateUser) {
                on<FakeResponse>(201) fires { UserCreated("u1", "a@b") }
                on<FakeResponse>(400) fires { UserCreationFailed("nope") }
            }
        }
        val compiled = RecipeCompiler.compileRecipe(r)
        val outputs = compiled.allEvents.map { it.name }.toSet()
        assertTrue(outputs.contains("UserCreated"))
        assertTrue(outputs.contains("UserCreationFailed"))
    }

    @Test
    fun `requires registers required events`() {
        val r = recipe("r") {
            sensoryEvents { event<SensoryEvent>() }
            api(CreateUser) {
                requires(UserCreated::class)
                on<FakeResponse>(201) fires { UserCreated("u1", "a@b") }
            }
        }
        val compiled = RecipeCompiler.compileRecipe(r)
        val interaction = compiled.interactionTransitions.single { it.interactionName == "CreateUser" }
        assertTrue(interaction.requiredEvents.contains("UserCreated"))
    }
}
```

- [ ] **Step 2: Run tests, confirm they fail**

Run: `mvn -pl baker-openapi/baker-openapi-dsl test -q`
Expected: compile error — `api` is unresolved.

- [ ] **Step 3: Add `addInteraction` to `RecipeBuilder`**

Open `core/baker-recipe-dsl-kotlin/src/main/kotlin/com/ing/baker/recipe/kotlindsl/KotlinDsl.kt`. Find the existing `interaction<T>` function at around line 97-99 and add this method right after it:

```kotlin
    /**
     * Adds a pre-built [Interaction] directly. Intended for DSL extensions that
     * construct their own [Interaction] (e.g. baker-openapi-dsl's `api(...)`).
     */
    fun addInteraction(interaction: Interaction) {
        interactions.add(interaction)
    }
```

(The `Interaction` import is already present in this file as `com.ing.baker.recipe.kotlindsl.Interaction`.)

- [ ] **Step 4: Update the tests to use the final DSL form**

The tests in Step 1 are written against `on<FakeResponse>(201) fires { ... }`, an infix-style form that requires runtime mapper invocation to learn the produced event class. We instead expose a typed form that captures both classes via reified type parameters — simpler to implement and equivalent in expressiveness.

Edit `ApiDslTest.kt` and replace **every** `on<FakeResponse>(NNN) fires { ... }` call with the typed form:

```kotlin
on<FakeResponse, UserCreated>(201) { _ -> UserCreated("u1", "a@b") }
on<FakeResponse, UserCreationFailed>(400) { _ -> UserCreationFailed("nope") }
```

- [ ] **Step 5: Implement `ApiDsl.kt`**

Write `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiDsl.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.kotlindsl.Event
import com.ing.baker.recipe.kotlindsl.Interaction
import com.ing.baker.recipe.kotlindsl.RecipeBuilder
import community.flock.wirespec.kotlin.Wirespec
import java.util.Optional
import kotlin.reflect.KClass
import kotlin.reflect.full.memberProperties
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.javaType

@DslMarker
annotation class ApiDslMarker

/**
 * Registers a Baker interaction in this recipe based on an OpenAPI [operation].
 * The [configure] block declares status → user-event mappers and optional Baker
 * controls (required events, ingredient name overrides, maximumInteractionCount).
 */
fun RecipeBuilder.api(
    operation: ApiOperation,
    configure: ApiInteractionScope.() -> Unit,
) {
    val scope = ApiInteractionScope(operation).apply(configure)
    addInteraction(scope.buildInteraction())
}

@ApiDslMarker
class ApiInteractionScope internal constructor(private val operation: ApiOperation) {

    @PublishedApi
    internal val mappers = mutableMapOf<Int, (Wirespec.Response<*>) -> Any>()

    @PublishedApi
    internal val outputEventClasses = mutableSetOf<KClass<*>>()

    private val requiredEvents = mutableSetOf<String>()
    private val ingredientNameOverridesMap = mutableMapOf<String, String>()
    private var maxInteractionCount: Int? = null

    /**
     * Maps responses of HTTP [status] to a user-defined event. The [mapper]
     * receives the wirespec response and returns a domain event instance.
     */
    inline fun <reified R : Wirespec.Response<*>, reified E : Any> on(
        status: Int,
        noinline mapper: (R) -> E,
    ) {
        @Suppress("UNCHECKED_CAST")
        mappers[status] = { resp -> mapper(resp as R) }
        outputEventClasses.add(E::class)
    }

    fun requires(vararg eventClasses: KClass<*>) {
        eventClasses.forEach { requiredEvents.add(it.simpleName!!) }
    }

    fun maximumInteractionCount(n: Int) {
        maxInteractionCount = n
    }

    fun ingredientNameOverrides(block: MutableMap<String, String>.() -> Unit) {
        ingredientNameOverridesMap.apply(block)
    }

    /** Read-only view of configured mappers, for binding at app startup. */
    val configuredMappers: Map<Int, (Wirespec.Response<*>) -> Any> get() = mappers.toMap()

    internal fun buildInteraction(): Interaction {
        val inputIngredients: Set<Ingredient> = operation.inputFields
            .map { Ingredient(it.name, it.type.java) }
            .toSet()
        val events: Set<Event> = outputEventClasses
            .map { it.toEvent() }
            .toSet()
        return Interaction.of(
            operation.operationName,
            operation.operationName,
            inputIngredients,
            events,
            requiredEvents,
            emptySet(),
            emptyMap(),
            ingredientNameOverridesMap.toMap(),
            emptyMap(),
            Optional.ofNullable(maxInteractionCount),
            Optional.empty(),
            false,
        )
    }
}

private fun KClass<*>.toEvent(): Event {
    val ctor = primaryConstructor
    val ingredients = if (ctor != null) {
        ctor.parameters.map { Ingredient(it.name, it.type.javaType) }
    } else {
        memberProperties.map { Ingredient(it.name, it.returnType.javaType) }
    }
    return Event(simpleName!!, ingredients, Optional.empty())
}
```

- [ ] **Step 6: Run tests, confirm pass**

Run: `mvn -pl core/baker-recipe-dsl-kotlin -am install -q` (rebuild upstream first because we modified `KotlinDsl.kt`), then `mvn -pl baker-openapi/baker-openapi-dsl test -q`.

Expected: `Tests run: 3, Failures: 0`.

- [ ] **Step 7: Commit**

```bash
git add core/baker-recipe-dsl-kotlin/src/main/kotlin/com/ing/baker/recipe/kotlindsl/KotlinDsl.kt \
        baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiDsl.kt \
        baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiDslTest.kt
git commit -m "feat: add api(operation) DSL with status-coded response mapping"
```

---

## Task 6: `ApiOperationBinding` — runtime factory

A small helper that pairs an `ApiOperation` with a transport/serialization combo and produces an `ApiOperationInteraction` ready to register with Baker.

**Files:**
- Create: `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationBinding.kt`
- Create: `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationBindingTest.kt`

- [ ] **Step 1: Write the failing test**

Write `baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationBindingTest.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import community.flock.wirespec.kotlin.Wirespec
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import kotlin.reflect.KClass

private class StubHandler : Wirespec.Handler
private class StubResponse(override val status: Int) : Wirespec.Response<Unit> {
    override val headers: Map<String, List<String>> = emptyMap()
    override fun getBody() = Unit
}

private object StubOp : ApiOperation {
    override val operationName = "Stub"
    override val inputFields: List<InputField> = emptyList()
    override val responseTypes: Map<Int, KClass<*>> = mapOf(200 to StubResponse::class)
    override val handlerClass = StubHandler::class
    override fun buildRequest(ingredients: Map<String, Any?>): Any = Unit
    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> = StubResponse(200)
}

class ApiOperationBindingTest {

    @Test
    fun `binding produces an ApiOperationInteraction with the operation name`() {
        val handler = StubHandler()
        val binding = ApiOperationBinding(StubOp, handler, mappers = mapOf(200 to { _ -> "ok" }))
        val interaction = binding.toInteractionInstance()
        assertEquals("Stub", interaction.name())
    }
}
```

- [ ] **Step 2: Run test, confirm fail**

Run: `mvn -pl baker-openapi/baker-openapi-dsl test -Dtest=ApiOperationBindingTest -q`
Expected: compile error — `ApiOperationBinding` does not exist.

- [ ] **Step 3: Implement the binding**

Write `baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationBinding.kt`:

```kotlin
package com.ing.baker.openapi.dsl

import com.ing.baker.runtime.javadsl.InteractionInstance
import community.flock.wirespec.kotlin.Wirespec

/**
 * Pairs an [ApiOperation] descriptor with the wirespec handler that knows how to
 * execute it, plus the status → event mappers from the recipe. Produces an
 * [InteractionInstance] for Baker to register at startup.
 *
 * Mappers can be empty if the caller intends to share mappers with the recipe
 * (which is the usual case — recipe owns the mapping). When `mappers` is empty
 * the binding will fail at execute() time; callers normally pass the same mapper
 * map they used in the recipe's `api(...) { ... }` block.
 */
class ApiOperationBinding(
    private val operation: ApiOperation,
    private val handler: Wirespec.Handler,
    private val mappers: Map<Int, (Wirespec.Response<*>) -> Any>,
) {
    fun toInteractionInstance(): InteractionInstance =
        ApiOperationInteraction(operation, handler, mappers)
}
```

- [ ] **Step 4: Run test, confirm pass**

Run: `mvn -pl baker-openapi/baker-openapi-dsl test -q`
Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add baker-openapi/baker-openapi-dsl/src/main/kotlin/com/ing/baker/openapi/dsl/ApiOperationBinding.kt \
        baker-openapi/baker-openapi-dsl/src/test/kotlin/com/ing/baker/openapi/dsl/ApiOperationBindingTest.kt
git commit -m "feat: add ApiOperationBinding factory"
```

---

## Task 7: `baker-openapi-emitter` module skeleton

**Files:**
- Create: `baker-openapi/baker-openapi-emitter/pom.xml`

- [ ] **Step 1: Write the pom**

Write `baker-openapi/baker-openapi-emitter/pom.xml` (mirrors `core/baker-wirespec/pom.xml`):

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
         xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
    <modelVersion>4.0.0</modelVersion>

    <parent>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker-openapi</artifactId>
        <version>5.1.0-SNAPSHOT</version>
        <relativePath>../pom.xml</relativePath>
    </parent>

    <artifactId>baker-openapi-emitter</artifactId>
    <name>Baker OpenAPI Emitter</name>
    <description>Wirespec LanguageEmitter that generates ApiOperation descriptor objects for use with baker-openapi-dsl</description>

    <dependencies>
        <dependency>
            <groupId>community.flock.wirespec.compiler</groupId>
            <artifactId>core-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>
        <dependency>
            <groupId>org.jetbrains</groupId>
            <artifactId>annotations</artifactId>
            <version>13.0</version>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-stdlib</artifactId>
        </dependency>

        <dependency>
            <groupId>org.junit.jupiter</groupId>
            <artifactId>junit-jupiter-engine</artifactId>
            <scope>test</scope>
        </dependency>
    </dependencies>

    <build>
        <testSourceDirectory>src/test/kotlin</testSourceDirectory>
        <plugins>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-compiler-plugin</artifactId>
                <configuration>
                    <source>${jvm.target}</source>
                    <target>${jvm.target}</target>
                </configuration>
            </plugin>
            <plugin>
                <groupId>org.jetbrains.kotlin</groupId>
                <artifactId>kotlin-maven-plugin</artifactId>
                <version>${kotlin.version}</version>
                <configuration>
                    <jvmTarget>${jvm.target}</jvmTarget>
                </configuration>
                <executions>
                    <execution>
                        <id>test-compile</id>
                        <goals><goal>test-compile</goal></goals>
                    </execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-surefire-plugin</artifactId>
                <configuration>
                    <skipTests>false</skipTests>
                </configuration>
            </plugin>
        </plugins>
    </build>
</project>
```

- [ ] **Step 2: Create source dirs**

```bash
mkdir -p baker-openapi/baker-openapi-emitter/src/main/java/com/ing/baker/openapi/emitter
mkdir -p baker-openapi/baker-openapi-emitter/src/test/kotlin/com/ing/baker/openapi/emitter
```

- [ ] **Step 3: Verify build**

Run: `mvn -pl baker-openapi/baker-openapi-emitter compile -q`
Expected: `BUILD SUCCESS`.

- [ ] **Step 4: Commit**

```bash
git add baker-openapi/baker-openapi-emitter/pom.xml
git commit -m "feat: add baker-openapi-emitter module skeleton"
```

---

## Task 8: `BakerOpenApiEmitter` — emit descriptor objects

Generates one `object <OperationName> : ApiOperation { ... }` file per endpoint. Models and endpoint classes are emitted by wirespec's standard emitter, not this one.

**Files:**
- Create: `baker-openapi/baker-openapi-emitter/src/main/java/com/ing/baker/openapi/emitter/BakerOpenApiEmitter.java`
- Create: `baker-openapi/baker-openapi-emitter/src/test/kotlin/com/ing/baker/openapi/emitter/BakerOpenApiEmitterTest.kt`

- [ ] **Step 1: Write the failing test**

Write `baker-openapi/baker-openapi-emitter/src/test/kotlin/com/ing/baker/openapi/emitter/BakerOpenApiEmitterTest.kt`:

```kotlin
package com.ing.baker.openapi.emitter

import arrow.core.NonEmptyList
import community.flock.wirespec.compiler.core.FileUri
import community.flock.wirespec.compiler.core.emit.PackageName
import community.flock.wirespec.compiler.core.parse.ast.*
import community.flock.wirespec.compiler.core.parse.ast.Reference.Primitive.Type.Precision
import community.flock.wirespec.compiler.utils.Logger
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Assertions.assertEquals
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
        // Package and imports
        assertTrue(src.contains("package com.example.generated.api"))
        assertTrue(src.contains("import com.ing.baker.openapi.dsl.ApiOperation"))
        assertTrue(src.contains("import com.ing.baker.openapi.dsl.InputField"))
        assertTrue(src.contains("import com.example.generated.endpoint.CreateUser"))
        // Object declaration
        assertTrue(src.contains("object CreateUser : ApiOperation"))
        assertTrue(src.contains("override val operationName = \"CreateUser\""))
        // Input fields flattened from body
        assertTrue(src.contains("InputField(\"firstName\", String::class)"))
        assertTrue(src.contains("InputField(\"email\", String::class)"))
        // Response types
        assertTrue(src.contains("201 to CreateUser.Response201::class"))
        assertTrue(src.contains("400 to CreateUser.Response400::class"))
        // handlerClass
        assertTrue(src.contains("override val handlerClass = CreateUser.Handler::class"))
        // File path
        assertEquals("com/example/generated/api/CreateUser.kt", emitted.file)
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
        assertTrue(src.contains("InputField(\"id\", String::class)"))
    }
}
```

- [ ] **Step 2: Run, confirm fail**

Run: `mvn -pl baker-openapi/baker-openapi-emitter test -q`
Expected: compile error — `BakerOpenApiEmitter` does not exist.

- [ ] **Step 3: Implement the emitter**

Write `baker-openapi/baker-openapi-emitter/src/main/java/com/ing/baker/openapi/emitter/BakerOpenApiEmitter.java`:

```java
package com.ing.baker.openapi.emitter;

import community.flock.wirespec.compiler.core.emit.Emitted;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.PackageName;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Channel;
import community.flock.wirespec.compiler.core.parse.ast.Definition;
import community.flock.wirespec.compiler.core.parse.ast.Endpoint;
import community.flock.wirespec.compiler.core.parse.ast.Enum;
import community.flock.wirespec.compiler.core.parse.ast.Field;
import community.flock.wirespec.compiler.core.parse.ast.Identifier;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import community.flock.wirespec.compiler.core.parse.ast.Reference;
import community.flock.wirespec.compiler.core.parse.ast.Refined;
import community.flock.wirespec.compiler.core.parse.ast.Type;
import community.flock.wirespec.compiler.core.parse.ast.Union;
import community.flock.wirespec.compiler.utils.Logger;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class BakerOpenApiEmitter extends LanguageEmitter {

    private final PackageName packageName;
    private Module currentModule;

    public BakerOpenApiEmitter(PackageName packageName) {
        this.packageName = packageName;
    }

    public BakerOpenApiEmitter() {
        this.packageName = null;
    }

    @NotNull @Override public String getSingleLineComment() { return "//"; }
    @NotNull @Override public FileExtension getExtension() { return FileExtension.Kotlin; }
    @Nullable @Override public Shared getShared() { return null; }
    @NotNull @Override public String notYetImplemented() { return ""; }

    @NotNull
    @Override
    public Emitted emit(@NotNull Definition definition, @NotNull Module module, @NotNull Logger logger) {
        this.currentModule = module;
        Emitted base = super.emit(definition, module, logger);
        if (packageName != null && !packageName.getValue().isEmpty() && definition instanceof Endpoint) {
            String dir = packageName.getValue().replace('.', '/') + "/api/";
            return new Emitted(dir + base.getFile(), base.getResult());
        }
        return base;
    }

    @NotNull @Override public String emit(@NotNull Identifier identifier) { return identifier.getValue(); }

    @NotNull
    @Override
    public String emit(@NotNull Endpoint endpoint) {
        String name = emit(endpoint.getIdentifier());

        StringBuilder sb = new StringBuilder();
        if (packageName != null && !packageName.getValue().isEmpty()) {
            sb.append("package ").append(packageName.getValue()).append(".api\n\n");
            sb.append("import ").append(packageName.getValue()).append(".endpoint.").append(name).append("\n");
        }
        sb.append("import com.ing.baker.openapi.dsl.ApiOperation\n");
        sb.append("import com.ing.baker.openapi.dsl.InputField\n");
        sb.append("import community.flock.wirespec.kotlin.Wirespec\n");
        sb.append("import kotlin.reflect.KClass\n\n");

        sb.append("object ").append(name).append(" : ApiOperation {\n");
        sb.append("    override val operationName = \"").append(name).append("\"\n\n");

        // Input fields: path + query + headers + flattened body fields
        List<String[]> inputs = collectInputs(endpoint);
        sb.append("    override val inputFields = listOf(\n");
        for (String[] f : inputs) {
            sb.append("        InputField(\"").append(f[0]).append("\", ").append(f[1]).append("::class),\n");
        }
        sb.append("    )\n\n");

        // Response types
        sb.append("    override val responseTypes: Map<Int, KClass<*>> = mapOf(\n");
        for (Endpoint.Response resp : endpoint.getResponses()) {
            sb.append("        ").append(resp.getStatus()).append(" to ").append(name)
              .append(".Response").append(resp.getStatus()).append("::class,\n");
        }
        sb.append("    )\n\n");

        // handlerClass
        sb.append("    override val handlerClass = ").append(name).append(".Handler::class\n\n");

        // buildRequest
        sb.append("    override fun buildRequest(ingredients: Map<String, Any?>): Any =\n");
        sb.append("        ").append(name).append(".Request(\n");
        // Path params first, then query, headers, body
        String bodyTypeName = bodyTypeName(endpoint);
        List<String> ctorArgs = new ArrayList<>();
        for (Endpoint.Segment seg : endpoint.getPath()) {
            if (seg instanceof Endpoint.Segment.Param p) {
                ctorArgs.add(p.getIdentifier().getValue() + " = ingredients[\"" + p.getIdentifier().getValue() + "\"] as " + kotlinType(p.getReference()));
            }
        }
        for (Field q : endpoint.getQueries()) {
            ctorArgs.add(q.getIdentifier().getValue() + " = ingredients[\"" + q.getIdentifier().getValue() + "\"] as " + kotlinType(q.getReference()));
        }
        for (Field h : endpoint.getHeaders()) {
            ctorArgs.add(h.getIdentifier().getValue() + " = ingredients[\"" + h.getIdentifier().getValue() + "\"] as " + kotlinType(h.getReference()));
        }
        if (bodyTypeName != null) {
            Type bodyType = findType(bodyTypeName);
            StringBuilder bodyCtor = new StringBuilder(bodyTypeName + "(");
            if (bodyType != null) {
                String fields = bodyType.getShape().getValue().stream()
                    .map(f -> f.getIdentifier().getValue() + " = ingredients[\"" + f.getIdentifier().getValue() + "\"] as " + kotlinType(f.getReference()))
                    .collect(Collectors.joining(", "));
                bodyCtor.append(fields);
            }
            bodyCtor.append(")");
            ctorArgs.add(bodyCtor.toString());
        }
        sb.append("            ").append(String.join(",\n            ", ctorArgs)).append("\n");
        sb.append("        )\n\n");

        // invoke
        String handlerMethod = Character.toLowerCase(name.charAt(0)) + name.substring(1);
        sb.append("    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> =\n");
        sb.append("        (handler as ").append(name).append(".Handler).").append(handlerMethod)
          .append("(request as ").append(name).append(".Request)\n");
        sb.append("}\n");

        return sb.toString();
    }

    @NotNull @Override public String emit(@NotNull Type type, @NotNull Module module) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Type.Shape shape) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Field field) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Reference reference) { return kotlinType(reference); }
    @NotNull @Override public String emit(@NotNull Reference.Primitive.Type.Constraint constraint) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Enum anEnum, @NotNull Module module) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Union union) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Refined refined) { return notYetImplemented(); }
    @NotNull @Override public String emitValidator(@NotNull Refined refined) { return notYetImplemented(); }
    @NotNull @Override public String emit(@NotNull Channel channel) { return notYetImplemented(); }

    private List<String[]> collectInputs(Endpoint endpoint) {
        List<String[]> out = new ArrayList<>();
        for (Endpoint.Segment seg : endpoint.getPath()) {
            if (seg instanceof Endpoint.Segment.Param p) {
                out.add(new String[]{p.getIdentifier().getValue(), kotlinType(p.getReference())});
            }
        }
        for (Field q : endpoint.getQueries()) {
            out.add(new String[]{q.getIdentifier().getValue(), kotlinType(q.getReference())});
        }
        for (Field h : endpoint.getHeaders()) {
            out.add(new String[]{h.getIdentifier().getValue(), kotlinType(h.getReference())});
        }
        for (Endpoint.Request req : endpoint.getRequests()) {
            if (req.getContent() != null && req.getContent().getReference() instanceof Reference.Custom c) {
                Type bodyType = findType(c.getValue());
                if (bodyType != null) {
                    for (Field f : bodyType.getShape().getValue()) {
                        out.add(new String[]{f.getIdentifier().getValue(), kotlinType(f.getReference())});
                    }
                }
            }
        }
        return out;
    }

    private String bodyTypeName(Endpoint endpoint) {
        for (Endpoint.Request req : endpoint.getRequests()) {
            if (req.getContent() != null && req.getContent().getReference() instanceof Reference.Custom c) {
                return c.getValue();
            }
        }
        return null;
    }

    private Type findType(String name) {
        if (currentModule == null) return null;
        for (var stmt : currentModule.getStatements()) {
            if (stmt instanceof Type t && t.getIdentifier().getValue().equals(name)) return t;
        }
        return null;
    }

    private String kotlinType(Reference ref) {
        String base;
        if (ref instanceof Reference.Primitive p) {
            base = switch (p.getType()) {
                case Reference.Primitive.Type.String s -> "String";
                case Reference.Primitive.Type.Integer i -> i.getPrecision().name().equals("P32") ? "Int" : "Long";
                case Reference.Primitive.Type.Number n -> n.getPrecision().name().equals("P32") ? "Float" : "Double";
                case Reference.Primitive.Type.Bytes b -> "ByteArray";
                default -> "Any";
            };
            // Boolean lookup workaround for name collision is not needed in switch since the Java compiler doesn't collide.
            if (p.getType().getClass().getSimpleName().equals("Boolean")) base = "Boolean";
        } else if (ref instanceof Reference.Custom c) {
            base = c.getValue();
        } else if (ref instanceof Reference.Iterable it) {
            base = "List<" + kotlinType(it.getReference()) + ">";
        } else if (ref instanceof Reference.Dict d) {
            base = "Map<String, " + kotlinType(d.getReference()) + ">";
        } else if (ref instanceof Reference.Unit) {
            base = "Unit";
        } else {
            base = "Any";
        }
        return ref.isNullable() ? base + "?" : base;
    }
}
```

- [ ] **Step 4: Run, confirm pass**

Run: `mvn -pl baker-openapi/baker-openapi-emitter test -q`
Expected: `Tests run: 2, Failures: 0`.

- [ ] **Step 5: Commit**

```bash
git add baker-openapi/baker-openapi-emitter/src
git commit -m "feat: add BakerOpenApiEmitter generating ApiOperation descriptors"
```

---

## Task 9: `baker-openapi-plugin` module skeleton

**Files:**
- Create: `baker-openapi/baker-openapi-plugin/pom.xml`

- [ ] **Step 1: Write the pom**

Write `baker-openapi/baker-openapi-plugin/pom.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0"
         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
         xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
    <modelVersion>4.0.0</modelVersion>

    <parent>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker-openapi</artifactId>
        <version>5.1.0-SNAPSHOT</version>
        <relativePath>../pom.xml</relativePath>
    </parent>

    <artifactId>baker-openapi-plugin</artifactId>
    <name>Baker OpenAPI Maven Plugin</name>
    <packaging>maven-plugin</packaging>

    <properties>
        <maven.api.version>3.9.6</maven.api.version>
    </properties>

    <dependencies>
        <dependency>
            <groupId>org.apache.maven</groupId>
            <artifactId>maven-plugin-api</artifactId>
            <version>${maven.api.version}</version>
            <scope>provided</scope>
        </dependency>
        <dependency>
            <groupId>org.apache.maven.plugin-tools</groupId>
            <artifactId>maven-plugin-annotations</artifactId>
            <version>3.10.2</version>
            <scope>provided</scope>
        </dependency>
        <dependency>
            <groupId>org.apache.maven</groupId>
            <artifactId>maven-core</artifactId>
            <version>${maven.api.version}</version>
            <scope>provided</scope>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-openapi-emitter</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>community.flock.wirespec.compiler</groupId>
            <artifactId>core-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>
        <dependency>
            <groupId>community.flock.wirespec.converter</groupId>
            <artifactId>openapi-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-stdlib</artifactId>
        </dependency>

        <dependency>
            <groupId>org.junit.jupiter</groupId>
            <artifactId>junit-jupiter-engine</artifactId>
            <scope>test</scope>
        </dependency>
    </dependencies>

    <build>
        <plugins>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-plugin-plugin</artifactId>
                <version>3.10.2</version>
                <executions>
                    <execution>
                        <id>default-descriptor</id>
                        <phase>process-classes</phase>
                    </execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-compiler-plugin</artifactId>
                <configuration>
                    <source>${jvm.target}</source>
                    <target>${jvm.target}</target>
                </configuration>
            </plugin>
        </plugins>
    </build>
</project>
```

- [ ] **Step 2: Create source dirs**

```bash
mkdir -p baker-openapi/baker-openapi-plugin/src/main/java/com/ing/baker/openapi/plugin
```

- [ ] **Step 3: Verify build (will fail until Task 10 adds a Mojo)**

Run: `mvn -pl baker-openapi/baker-openapi-plugin compile -q`
Expected: `BUILD SUCCESS` (no sources yet; maven-plugin-plugin runs in `process-classes`).

- [ ] **Step 4: Commit**

```bash
git add baker-openapi/baker-openapi-plugin/pom.xml
git commit -m "feat: add baker-openapi-plugin module skeleton"
```

---

## Task 10: `GenerateFromOpenApiMojo` + integration test

The Mojo invokes wirespec's `convert` entry point with two emitters (the standard Kotlin emitter + `BakerOpenApiEmitter`).

**Files:**
- Create: `baker-openapi/baker-openapi-plugin/src/main/java/com/ing/baker/openapi/plugin/GenerateFromOpenApiMojo.java`
- Create: `baker-openapi/baker-openapi-plugin/src/it/settings.xml`
- Create: `baker-openapi/baker-openapi-plugin/src/it/happy-path/pom.xml`
- Create: `baker-openapi/baker-openapi-plugin/src/it/happy-path/src/main/openapi/petstore.json`
- Create: `baker-openapi/baker-openapi-plugin/src/it/happy-path/verify.groovy`
- Modify: `baker-openapi/baker-openapi-plugin/pom.xml` (add `maven-invoker-plugin` to run `src/it/`)

- [ ] **Step 1: Implement the Mojo**

Write `baker-openapi/baker-openapi-plugin/src/main/java/com/ing/baker/openapi/plugin/GenerateFromOpenApiMojo.java`:

```java
package com.ing.baker.openapi.plugin;

import arrow.core.NonEmptyList;
import arrow.core.NonEmptySet;
import com.ing.baker.openapi.emitter.BakerOpenApiEmitter;
import community.flock.wirespec.compiler.core.emit.EmitShared;
import community.flock.wirespec.compiler.core.emit.Emitted;
import community.flock.wirespec.compiler.core.emit.Emitter;
import community.flock.wirespec.compiler.core.emit.PackageName;
import community.flock.wirespec.compiler.core.emit.KotlinEmitter;
import community.flock.wirespec.compiler.utils.Logger;
import community.flock.wirespec.openapi.v3.OpenAPIV3Parser;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.project.MavenProject;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

@Mojo(name = "generate-from-openapi", defaultPhase = LifecyclePhase.GENERATE_SOURCES, threadSafe = true)
public class GenerateFromOpenApiMojo extends AbstractMojo {

    @Parameter(required = true)
    private String input;

    @Parameter(required = true)
    private String packageName;

    @Parameter(defaultValue = "${project.build.directory}/generated-sources/baker-openapi")
    private String outputDirectory;

    @Parameter(defaultValue = "true")
    private boolean addToSources;

    @Parameter(defaultValue = "${project}", readonly = true, required = true)
    private MavenProject project;

    private final Logger logger = new Logger(Logger.Level.INFO) {
        @Override public void debug(String s) { getLog().debug(s); }
        @Override public void info(String s)  { getLog().info(s); }
        @Override public void warn(String s)  { getLog().warn(s); }
        @Override public void error(String s) { getLog().error(s); }
    };

    @Override
    public void execute() throws MojoExecutionException {
        try {
            Path inputPath = Paths.get(input);
            if (!Files.exists(inputPath)) {
                throw new MojoExecutionException("OpenAPI file not found: " + input);
            }
            String json = Files.readString(inputPath);
            PackageName pkg = new PackageName(packageName);

            // Parse OpenAPI → wirespec module list
            List<Module> modules = OpenAPIV3Parser.INSTANCE.parse(json, false);

            // Standard Kotlin emitter for models + endpoint classes
            KotlinEmitter kotlinEmitter = new KotlinEmitter(pkg, new EmitShared(false));
            // Baker descriptor emitter
            BakerOpenApiEmitter bakerEmitter = new BakerOpenApiEmitter(pkg);

            Path outDir = Paths.get(outputDirectory);
            Files.createDirectories(outDir);

            for (Module module : modules) {
                emitAll(module, kotlinEmitter, outDir);
                emitAll(module, bakerEmitter, outDir);
            }

            if (addToSources) {
                project.addCompileSourceRoot(outDir.toString());
                getLog().info("Added " + outDir + " as compile source root");
            }
        } catch (IOException e) {
            throw new MojoExecutionException("Failed to read OpenAPI input", e);
        } catch (RuntimeException e) {
            throw new MojoExecutionException("Generation failed", e);
        }
    }

    private void emitAll(Module module, Emitter emitter, Path outDir) throws IOException {
        // Wirespec emitters expose emit(Definition, Module, Logger). Iterate the module's statements.
        for (var stmt : module.getStatements()) {
            Emitted emitted = emitter.emit(stmt, module, logger);
            if (emitted.getResult() == null || emitted.getResult().isBlank()) continue;
            Path target = outDir.resolve(emitted.getFile());
            Files.createDirectories(target.getParent());
            Files.writeString(target, emitted.getResult());
        }
    }
}
```

Note: the exact wirespec API surface for emitting an entire module may differ. If `OpenAPIV3Parser.parse(...)` or the iteration shape doesn't match this signature in the imported jar, follow the `ConvertMojo.kt` reference at `/tmp/wirespec-mvn-src/community/flock/wirespec/plugin/maven/mojo/ConvertMojo.kt` and adapt. The plan-level intent is: parse OpenAPI → wirespec AST modules, run both emitters, write `emitted.file → emitted.result` under `outDir`.

- [ ] **Step 2: Build the plugin**

Run: `mvn -pl baker-openapi/baker-openapi-plugin -am install -q`
Expected: `BUILD SUCCESS`. The plugin descriptor (`META-INF/maven/plugin.xml`) is generated automatically by `maven-plugin-plugin`.

- [ ] **Step 3: Add an integration test harness — modify the plugin pom**

In `baker-openapi/baker-openapi-plugin/pom.xml`, add this plugin entry inside `<build><plugins>`:

```xml
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-invoker-plugin</artifactId>
                <version>3.7.0</version>
                <configuration>
                    <projectsDirectory>src/it</projectsDirectory>
                    <cloneProjectsTo>${project.build.directory}/it</cloneProjectsTo>
                    <settingsFile>src/it/settings.xml</settingsFile>
                    <postBuildHookScript>verify</postBuildHookScript>
                    <streamLogs>true</streamLogs>
                    <goals><goal>generate-sources</goal></goals>
                </configuration>
                <executions>
                    <execution>
                        <id>integration-test</id>
                        <goals>
                            <goal>install</goal>
                            <goal>run</goal>
                        </goals>
                    </execution>
                </executions>
            </plugin>
```

- [ ] **Step 4: Create the invoker settings file**

Write `baker-openapi/baker-openapi-plugin/src/it/settings.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<settings xmlns="http://maven.apache.org/SETTINGS/1.0.0"
          xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
          xsi:schemaLocation="http://maven.apache.org/SETTINGS/1.0.0 http://maven.apache.org/xsd/settings-1.0.0.xsd">
    <profiles>
        <profile>
            <id>it-repo</id>
            <activation><activeByDefault>true</activeByDefault></activation>
        </profile>
    </profiles>
</settings>
```

- [ ] **Step 5: Add the IT project**

Write `baker-openapi/baker-openapi-plugin/src/it/happy-path/pom.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0">
    <modelVersion>4.0.0</modelVersion>
    <groupId>com.ing.baker.it</groupId>
    <artifactId>happy-path</artifactId>
    <version>1.0.0</version>
    <packaging>jar</packaging>

    <build>
        <plugins>
            <plugin>
                <groupId>com.ing.baker</groupId>
                <artifactId>baker-openapi-plugin</artifactId>
                <version>@project.version@</version>
                <executions>
                    <execution>
                        <goals><goal>generate-from-openapi</goal></goals>
                        <configuration>
                            <input>${project.basedir}/src/main/openapi/petstore.json</input>
                            <packageName>com.example.it</packageName>
                        </configuration>
                    </execution>
                </executions>
            </plugin>
        </plugins>
    </build>
</project>
```

Write `baker-openapi/baker-openapi-plugin/src/it/happy-path/src/main/openapi/petstore.json` — a minimal OpenAPI v3 document with one POST operation:

```json
{
  "openapi": "3.0.0",
  "info": {"title": "Petstore", "version": "1.0.0"},
  "paths": {
    "/pets": {
      "post": {
        "operationId": "addPet",
        "requestBody": {
          "required": true,
          "content": {
            "application/json": {
              "schema": {"$ref": "#/components/schemas/Pet"}
            }
          }
        },
        "responses": {
          "201": {
            "description": "Created",
            "content": {
              "application/json": {
                "schema": {"$ref": "#/components/schemas/Pet"}
              }
            }
          }
        }
      }
    }
  },
  "components": {
    "schemas": {
      "Pet": {
        "type": "object",
        "required": ["name"],
        "properties": {
          "id": {"type": "string"},
          "name": {"type": "string"}
        }
      }
    }
  }
}
```

Write `baker-openapi/baker-openapi-plugin/src/it/happy-path/verify.groovy`:

```groovy
def base = new File(basedir, "target/generated-sources/baker-openapi/com/example/it")
assert new File(base, "model/Pet.kt").exists() : "Pet model file missing"
assert new File(base, "endpoint/AddPet.kt").exists() : "AddPet endpoint file missing"

def descriptor = new File(base, "api/AddPet.kt")
assert descriptor.exists() : "Descriptor file missing"
def text = descriptor.text
assert text.contains("object AddPet : ApiOperation") : "Descriptor object declaration missing"
assert text.contains('override val operationName = "AddPet"') : "operationName missing"
assert text.contains("InputField(\"name\", String::class)") : "InputField for name missing"
assert text.contains("201 to AddPet.Response201::class") : "response 201 mapping missing"
return true
```

- [ ] **Step 6: Run the integration test**

Run: `mvn -pl baker-openapi/baker-openapi-plugin -am verify -q`
Expected: `BUILD SUCCESS`. The IT writes the generated files and `verify.groovy` confirms their content.

If wirespec's OpenAPI parser raises an error on the minimal Petstore JSON (some versions require `info.description`, schemes, etc.), expand the fixture until the parser accepts it. Keep the operation count at one to minimize fixture maintenance.

- [ ] **Step 7: Commit**

```bash
git add baker-openapi/baker-openapi-plugin
git commit -m "feat: add baker-openapi Maven plugin with generate-from-openapi goal"
```

---

## Task 11: End-to-end example — `examples/baker-openapi-example`

Builds confidence the whole stack works. Mirrors the existing `baker-wirespec-example` structure but uses the new DSL.

**Files:**
- Create: `examples/baker-openapi-example/pom.xml`
- Create: `examples/baker-openapi-example/src/main/openapi/account-api.json`
- Create: `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/Events.kt`
- Create: `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/Transportation.kt`
- Create: `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/AccountRecipe.kt`
- Create: `examples/baker-openapi-example/src/test/kotlin/com/ing/baker/examples/account/openapi/AccountRecipeWireMockTest.kt`
- Modify: root `pom.xml` (register example module near other examples)

- [ ] **Step 1: Add the example pom**

Write `examples/baker-openapi-example/pom.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0">
    <modelVersion>4.0.0</modelVersion>

    <parent>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker</artifactId>
        <version>5.1.0-SNAPSHOT</version>
        <relativePath>../../pom.xml</relativePath>
    </parent>

    <artifactId>baker-openapi-example</artifactId>
    <name>Baker OpenAPI Example</name>

    <properties>
        <wirespec.version>0.17.20</wirespec.version>
    </properties>

    <dependencies>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-openapi-dsl</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-interface-kotlin</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-recipe-dsl-kotlin</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-compiler</artifactId>
            <version>${project.version}</version>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-stdlib</artifactId>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlinx</groupId>
            <artifactId>kotlinx-coroutines-core</artifactId>
        </dependency>
        <dependency>
            <groupId>community.flock.wirespec.integration</groupId>
            <artifactId>wirespec-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>
        <dependency>
            <groupId>community.flock.wirespec.integration</groupId>
            <artifactId>jackson-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>
        <dependency>
            <groupId>com.fasterxml.jackson.core</groupId>
            <artifactId>jackson-databind</artifactId>
            <version>2.18.2</version>
        </dependency>
        <dependency>
            <groupId>com.fasterxml.jackson.module</groupId>
            <artifactId>jackson-module-kotlin</artifactId>
            <version>2.18.2</version>
        </dependency>

        <dependency>
            <groupId>org.wiremock</groupId>
            <artifactId>wiremock</artifactId>
            <version>3.12.1</version>
            <scope>test</scope>
        </dependency>
        <dependency>
            <groupId>org.junit.jupiter</groupId>
            <artifactId>junit-jupiter-engine</artifactId>
            <scope>test</scope>
        </dependency>
        <dependency>
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlin-test-junit5</artifactId>
            <version>${kotlin.version}</version>
            <scope>test</scope>
        </dependency>
    </dependencies>

    <build>
        <plugins>
            <plugin>
                <groupId>com.ing.baker</groupId>
                <artifactId>baker-openapi-plugin</artifactId>
                <version>${project.version}</version>
                <executions>
                    <execution>
                        <id>account-api</id>
                        <goals><goal>generate-from-openapi</goal></goals>
                        <configuration>
                            <input>${project.basedir}/src/main/openapi/account-api.json</input>
                            <packageName>com.ing.baker.examples.account.openapi.generated</packageName>
                        </configuration>
                    </execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.codehaus.mojo</groupId>
                <artifactId>build-helper-maven-plugin</artifactId>
                <executions>
                    <execution>
                        <id>add-source</id>
                        <phase>generate-sources</phase>
                        <goals><goal>add-source</goal></goals>
                        <configuration>
                            <sources>
                                <source>src/main/kotlin</source>
                            </sources>
                        </configuration>
                    </execution>
                    <execution>
                        <id>add-test-source</id>
                        <phase>generate-test-sources</phase>
                        <goals><goal>add-test-source</goal></goals>
                        <configuration>
                            <sources>
                                <source>src/test/kotlin</source>
                            </sources>
                        </configuration>
                    </execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.jetbrains.kotlin</groupId>
                <artifactId>kotlin-maven-plugin</artifactId>
                <version>${kotlin.version}</version>
                <configuration><jvmTarget>${jvm.target}</jvmTarget></configuration>
                <executions>
                    <execution><id>compile</id><phase>process-sources</phase><goals><goal>compile</goal></goals></execution>
                    <execution><id>test-compile</id><phase>process-test-sources</phase><goals><goal>test-compile</goal></goals></execution>
                </executions>
            </plugin>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-deploy-plugin</artifactId>
                <configuration><skip>true</skip></configuration>
            </plugin>
        </plugins>
    </build>
</project>
```

- [ ] **Step 2: Register the example in the root pom**

Find the line `<module>examples/baker-wirespec-example</module>` in root `pom.xml` and add the new example right after it:

```xml
        <module>examples/baker-wirespec-example</module>
        <module>examples/baker-openapi-example</module>
```

- [ ] **Step 3: Add a minimal OpenAPI doc**

Write `examples/baker-openapi-example/src/main/openapi/account-api.json` — copy the equivalent operations from the existing `baker-wirespec-example/src/main/wirespec/account.ws` and translate to OpenAPI. At minimum it needs a `POST /accounts` operation returning `201 → AccountDto` / `400 → ErrorResponse`. If unsure of the exact shape, mirror `examples/baker-wirespec-example/src/main/openapi/profile-api.json` (already in repo) as a template.

- [ ] **Step 4: Add user-defined events**

Write `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/Events.kt`:

```kotlin
package com.ing.baker.examples.account.openapi

data class CreateAccountCommand(
    val userId: String,
    val profileId: String,
    val accountType: String,
    val currency: String,
)

data class AccountCreated(val accountId: String, val iban: String)
data class AccountCreationFailed(val reason: String)
```

- [ ] **Step 5: Copy the transport helper**

Write `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/Transportation.kt` — copy verbatim from `examples/baker-wirespec-example/src/main/kotlin/com/ing/baker/examples/account/Transportation.kt`, changing only the package to `com.ing.baker.examples.account.openapi`.

- [ ] **Step 6: Write the recipe using the new DSL**

Write `examples/baker-openapi-example/src/main/kotlin/com/ing/baker/examples/account/openapi/AccountRecipe.kt`:

```kotlin
package com.ing.baker.examples.account.openapi

import com.ing.baker.openapi.dsl.api
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import com.ing.baker.examples.account.openapi.generated.api.CreateAccount
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint

@OptIn(ExperimentalDsl::class)
object AccountRecipe {
    val recipe = recipe("OpenApiAccount") {
        sensoryEvents { event<CreateAccountCommand>() }

        api(CreateAccount) {
            on<CreateAccountEndpoint.Response201, AccountCreated>(201) { resp ->
                val body = resp.body
                AccountCreated(accountId = body.accountId, iban = body.iban)
            }
            on<CreateAccountEndpoint.Response400, AccountCreationFailed>(400) { resp ->
                AccountCreationFailed(reason = resp.body.message)
            }
        }
    }
}
```

- [ ] **Step 7: Write the WireMock end-to-end test**

Write `examples/baker-openapi-example/src/test/kotlin/com/ing/baker/examples/account/openapi/AccountRecipeWireMockTest.kt` — adapt from `examples/baker-wirespec-example/src/test/kotlin/com/ing/baker/examples/account/CreateCurrentAccountWireMockTest.kt`. Key shape:

```kotlin
package com.ing.baker.examples.account.openapi

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.*
import com.github.tomakehurst.wiremock.core.WireMockConfiguration.wireMockConfig
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.examples.account.openapi.generated.api.CreateAccount
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint
import com.ing.baker.openapi.dsl.ApiOperationBinding
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.runtime.javadsl.EventInstance
import com.ing.baker.runtime.kotlindsl.InMemoryBaker
import community.flock.wirespec.integration.jackson.kotlin.WirespecSerialization
import community.flock.wirespec.kotlin.Wirespec
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.*
import java.util.UUID
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

@OptIn(ExperimentalDsl::class)
class AccountRecipeWireMockTest {

    private lateinit var server: WireMockServer
    private lateinit var transport: Transportation
    private val objectMapper = ObjectMapper().registerKotlinModule()
    private val serialization = WirespecSerialization(objectMapper)

    @BeforeEach fun setUp() {
        server = WireMockServer(wireMockConfig().dynamicPort()).also { it.start() }
        transport = javaHttpTransportation("http://localhost:${server.port()}")
    }
    @AfterEach fun tearDown() { server.stop() }

    private fun createAccountHandler(): CreateAccountEndpoint.Handler {
        val edge = CreateAccountEndpoint.Handler.client(serialization)
        return object : CreateAccountEndpoint.Handler {
            override suspend fun createAccount(request: CreateAccountEndpoint.Request): CreateAccountEndpoint.Response<*> =
                edge.from(transport(edge.to(request)))
        }
    }

    @Test
    fun `recipe fires AccountCreated on 201`() = runBlocking {
        server.stubFor(post(urlEqualTo("/accounts")).willReturn(
            aResponse().withStatus(201).withHeader("Content-Type", "application/json")
                .withBody(objectMapper.writeValueAsString(mapOf(
                    "accountId" to "a1", "userId" to "u1", "profileId" to "p1",
                    "iban" to "NL00", "accountType" to "CURRENT", "currency" to "EUR",
                )))
        ))

        val handler = createAccountHandler()
        val mappers: Map<Int, (Wirespec.Response<*>) -> Any> = mapOf(
            201 to { resp -> (resp as CreateAccountEndpoint.Response201).let { AccountCreated(it.body.accountId, it.body.iban) } },
            400 to { resp -> (resp as CreateAccountEndpoint.Response400).let { AccountCreationFailed(it.body.message) } },
        )
        val binding = ApiOperationBinding(CreateAccount, handler, mappers)

        val baker = InMemoryBaker.kotlin(implementations = listOf(binding.toInteractionInstance()))
        val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(AccountRecipe.recipe), validate = true)
        val rid = UUID.randomUUID().toString()
        baker.bake(recipeId, rid)
        baker.fireSensoryEventAndAwaitReceived(rid, EventInstance.from(
            CreateAccountCommand("u1", "p1", "CURRENT", "EUR")
        ))
        baker.awaitCompleted(rid, timeout = 10.seconds)

        val events = baker.getRecipeInstanceState(rid).events.map { it.name }
        assertTrue(events.contains("AccountCreated"))
        server.verify(postRequestedFor(urlEqualTo("/accounts")))
    }
}
```

- [ ] **Step 8: Run the example end-to-end**

Run: `mvn -pl examples/baker-openapi-example -am verify -q`
Expected: `BUILD SUCCESS`, one test passes.

- [ ] **Step 9: Commit**

```bash
git add examples/baker-openapi-example pom.xml
git commit -m "feat: add baker-openapi-example demonstrating new DSL end to end"
```

---

## Final verification

- [ ] **Step 1: Build everything from a clean state**

Run: `mvn clean install -q -pl baker-openapi,examples/baker-openapi-example -am`
Expected: `BUILD SUCCESS`.

- [ ] **Step 2: Run full test suite on the new modules**

Run: `mvn test -pl baker-openapi/baker-openapi-dsl,baker-openapi/baker-openapi-emitter,baker-openapi/baker-openapi-plugin,examples/baker-openapi-example -q`
Expected: all tests pass.

- [ ] **Step 3: Verify the existing baker-wirespec test suite still passes (regression check)**

Run: `mvn test -pl core/baker-wirespec,examples/baker-wirespec-example -q`
Expected: `BUILD SUCCESS` — confirms the upstream `KotlinDsl.kt` change in Task 5 didn't break the existing emitter or example.

- [ ] **Step 4: Final commit if anything was adjusted**

If any pom or fixture needed tweaking during final verification:

```bash
git add -p
git commit -m "chore: post-integration adjustments"
```

---

## Notes for the implementer

- **Wirespec API drift:** The exact entry points (`OpenAPIV3Parser.parse`, `KotlinEmitter` constructor, `Module.getStatements`) are taken from wirespec 0.17.20 sources extracted into `/tmp/wirespec-mvn-src/` during plan authoring. If a method signature mismatch appears at Task 10, consult `ConvertMojo.kt` and the `core-jvm` jar's public API via `unzip -l ... | grep "\.class$"` — the intent is unchanged: parse → emit modules → write files.
- **`@PublishedApi internal` access:** Task 5 sidesteps this by adding a public `addInteraction` method to `RecipeBuilder`. Do not try to bypass via `inline` — that would force the DSL surface to be all-inline and complicate the implementation.
- **Existing `baker-wirespec` module:** Untouched by this plan. Mark it `@Deprecated` only after Task 11's example is green and reviewed (out of scope for this plan; track as a follow-up).
- **Hand-written tests with fakes (FakeHandler/FakeResponse):** Task 4 and Task 5 tests use local fakes so they don't depend on Task 8's generated descriptors. This keeps tasks independent.
