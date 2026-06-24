# Wirespec-Baker Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a `baker-wirespec` Maven module containing custom wirespec emitters that generate Baker Interaction interfaces and implementations from wirespec endpoint definitions.

**Architecture:** Two custom emitters (`BakerKotlinEmitter`, `BakerJavaEmitter`) extend wirespec's `LanguageEmitter`. They process only `Endpoint` AST nodes, generating Baker `Interaction` interfaces with sealed outcome events (one per HTTP status code) and implementation classes that bridge to wirespec's generated endpoint client code. All other AST node types return no-op output.

**Tech Stack:** Java 21, Kotlin 2.2.20, wirespec compiler core (`community.flock.wirespec.compiler:core-jvm:0.17.20`), Baker recipe DSL, JUnit 5 for testing.

---

## File Structure

```
baker-wirespec/
├── pom.xml
├── src/main/java/com/ing/baker/recipe/wirespec/
│   ├── BakerKotlinEmitter.java
│   └── BakerJavaEmitter.java
└── src/test/java/com/ing/baker/recipe/wirespec/
    ├── BakerKotlinEmitterTest.java
    └── BakerJavaEmitterTest.java
```

| File | Responsibility |
|------|---------------|
| `pom.xml` | Module build config: depends on wirespec compiler core |
| `BakerKotlinEmitter.java` | Extends `LanguageEmitter`, emits `.kt` files with Kotlin interaction interfaces + implementations |
| `BakerJavaEmitter.java` | Extends `LanguageEmitter`, emits `.java` files with Java interaction interfaces + implementations using `@FiresEvent` |
| `BakerKotlinEmitterTest.java` | Tests Kotlin emitter output against expected generated code |
| `BakerJavaEmitterTest.java` | Tests Java emitter output against expected generated code |

---

### Task 1: Create the Maven module

**Files:**
- Create: `baker-wirespec/pom.xml`
- Modify: `pom.xml` (root — add module entry)

- [ ] **Step 1: Create `baker-wirespec/pom.xml`**

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

    <artifactId>baker-wirespec</artifactId>
    <name>Baker Wirespec</name>
    <description>Wirespec emitters that generate Baker Interaction interfaces from API endpoint definitions</description>

    <properties>
        <wirespec.version>0.17.20</wirespec.version>
    </properties>

    <dependencies>
        <!-- Wirespec compiler core — LanguageEmitter, AST nodes -->
        <dependency>
            <groupId>community.flock.wirespec.compiler</groupId>
            <artifactId>core-jvm</artifactId>
            <version>${wirespec.version}</version>
        </dependency>

        <!-- JUnit 5 for tests -->
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
                <artifactId>maven-compiler-plugin</artifactId>
                <configuration>
                    <source>${jvm.target}</source>
                    <target>${jvm.target}</target>
                </configuration>
            </plugin>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-surefire-plugin</artifactId>
            </plugin>
        </plugins>
    </build>
</project>
```

- [ ] **Step 2: Add the module to the root `pom.xml`**

In `pom.xml` (root), add `<module>baker-wirespec</module>` to the `<modules>` section, after the existing modules.

- [ ] **Step 3: Verify the module builds**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec compile -q`
Expected: BUILD SUCCESS (empty module compiles)

- [ ] **Step 4: Commit**

```bash
git add baker-wirespec/pom.xml pom.xml
git commit -m "feat: add baker-wirespec module skeleton"
```

---

### Task 2: Implement `BakerKotlinEmitter` — scaffold with no-op methods

**Files:**
- Create: `baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitter.java`

- [ ] **Step 1: Create `BakerKotlinEmitter.java` with all required overrides returning no-op**

This establishes the emitter contract. All methods return empty/no-op. Endpoint emission will be implemented in the next task.

```java
package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Channel;
import community.flock.wirespec.compiler.core.parse.ast.Endpoint;
import community.flock.wirespec.compiler.core.parse.ast.Enum;
import community.flock.wirespec.compiler.core.parse.ast.Field;
import community.flock.wirespec.compiler.core.parse.ast.Identifier;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import community.flock.wirespec.compiler.core.parse.ast.Reference;
import community.flock.wirespec.compiler.core.parse.ast.Refined;
import community.flock.wirespec.compiler.core.parse.ast.Type;
import community.flock.wirespec.compiler.core.parse.ast.Union;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class BakerKotlinEmitter extends LanguageEmitter {

    @NotNull
    @Override
    public String getSingleLineComment() {
        return "//";
    }

    @NotNull
    @Override
    public FileExtension getExtension() {
        return FileExtension.Kotlin;
    }

    @Nullable
    @Override
    public Shared getShared() {
        return null;
    }

    @NotNull
    @Override
    public String notYetImplemented() {
        return "";
    }

    @NotNull
    @Override
    public String emit(@NotNull Identifier identifier) {
        return identifier.getValue();
    }

    @NotNull
    @Override
    public String emit(@NotNull Endpoint endpoint) {
        return ""; // implemented in Task 3
    }

    @NotNull
    @Override
    public String emit(@NotNull Type type, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Type.Shape shape) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Field field) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference reference) {
        return emitReference(reference);
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference.Primitive.Type.Constraint constraint) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Enum anEnum, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Union union) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emitValidator(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Channel channel) {
        return notYetImplemented();
    }

    /**
     * Maps wirespec Reference types to Kotlin type names.
     */
    private String emitReference(Reference reference) {
        String typeName;
        if (reference instanceof Reference.Primitive primitive) {
            typeName = switch (primitive.getType()) {
                case Reference.Primitive.Type.String s -> "String";
                case Reference.Primitive.Type.Integer i -> switch (i.getPrecision()) {
                    case P32 -> "Int";
                    case P64 -> "Long";
                };
                case Reference.Primitive.Type.Number n -> switch (n.getPrecision()) {
                    case P32 -> "Float";
                    case P64 -> "Double";
                };
                case Reference.Primitive.Type.Boolean b -> "Boolean";
                case Reference.Primitive.Type.Bytes b -> "ByteArray";
                default -> "Any";
            };
        } else if (reference instanceof Reference.Custom custom) {
            typeName = custom.getValue();
        } else if (reference instanceof Reference.Iterable iterable) {
            typeName = "List<" + emitReference(iterable.getReference()) + ">";
        } else if (reference instanceof Reference.Dict dict) {
            typeName = "Map<String, " + emitReference(dict.getReference()) + ">";
        } else if (reference instanceof Reference.Unit u) {
            typeName = "Unit";
        } else {
            typeName = "Any";
        }
        return reference.isNullable() ? typeName + "?" : typeName;
    }
}
```

- [ ] **Step 2: Verify it compiles**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec compile -q`
Expected: BUILD SUCCESS

- [ ] **Step 3: Commit**

```bash
git add baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitter.java
git commit -m "feat: add BakerKotlinEmitter scaffold with type mapping"
```

---

### Task 3: Implement `BakerKotlinEmitter.emit(Endpoint)` — Kotlin interaction generation

**Files:**
- Modify: `baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitter.java`
- Create: `baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitterTest.java`

- [ ] **Step 1: Write the test**

```java
package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.parse.ast.*;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

class BakerKotlinEmitterTest {

    private final BakerKotlinEmitter emitter = new BakerKotlinEmitter();

    @Test
    void emitSimpleGetEndpoint() {
        // GET /todos/{id: Integer} -> { 200 -> TodoDto, 404 -> ErrorDto }
        Endpoint endpoint = new Endpoint(
            null, // comment
            List.of(), // annotations
            new DefinitionIdentifier("GetTodo"),
            Endpoint.Method.GET,
            List.of(
                new Endpoint.Segment.Literal("/todos/"),
                new Endpoint.Segment.Param(
                    new FieldIdentifier("id"),
                    new Reference.Primitive(
                        new Reference.Primitive.Type.Integer(Reference.Primitive.Type.Precision.P64, null),
                        false
                    )
                )
            ),
            List.of(), // queries
            List.of(), // headers
            List.of(new Endpoint.Request(null)), // requests (no body)
            List.of(
                new Endpoint.Response(
                    "200",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("TodoDto", false)),
                    List.of()
                ),
                new Endpoint.Response(
                    "404",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("ErrorDto", false)),
                    List.of()
                )
            )
        );

        String result = emitter.emit(endpoint);

        String expected = """
                import com.ing.baker.recipe.javadsl.Interaction

                interface GetTodoInteraction : Interaction {
                    sealed interface GetTodoOutcome
                    data class GetTodoResponse200(val body: TodoDto) : GetTodoOutcome
                    data class GetTodoResponse404(val body: ErrorDto) : GetTodoOutcome

                    fun apply(id: Long): GetTodoOutcome
                }

                class GetTodoInteractionImpl(
                    private val client: GetTodo.Handler
                ) : GetTodoInteraction {
                    override fun apply(id: Long): GetTodoInteraction.GetTodoOutcome {
                        val request = GetTodo.Request(id)
                        val response = client.getTodo(request)
                        return when (response) {
                            is GetTodo.Response200 -> GetTodoInteraction.GetTodoResponse200(response.body)
                            is GetTodo.Response404 -> GetTodoInteraction.GetTodoResponse404(response.body)
                        }
                    }
                }
                """;

        assertEquals(expected.strip(), result.strip());
    }

    @Test
    void emitPostEndpointWithBody() {
        // POST /todos CreateTodoRequest -> { 201 -> TodoDto, 400 -> ErrorDto }
        Endpoint endpoint = new Endpoint(
            null,
            List.of(),
            new DefinitionIdentifier("CreateTodo"),
            Endpoint.Method.POST,
            List.of(new Endpoint.Segment.Literal("/todos")),
            List.of(), // queries
            List.of(), // headers
            List.of(new Endpoint.Request(
                new Endpoint.Content("application/json", new Reference.Custom("CreateTodoRequest", false))
            )),
            List.of(
                new Endpoint.Response(
                    "201",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("TodoDto", false)),
                    List.of()
                ),
                new Endpoint.Response(
                    "400",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("ErrorDto", false)),
                    List.of()
                )
            )
        );

        String result = emitter.emit(endpoint);

        String expected = """
                import com.ing.baker.recipe.javadsl.Interaction

                interface CreateTodoInteraction : Interaction {
                    sealed interface CreateTodoOutcome
                    data class CreateTodoResponse201(val body: TodoDto) : CreateTodoOutcome
                    data class CreateTodoResponse400(val body: ErrorDto) : CreateTodoOutcome

                    fun apply(body: CreateTodoRequest): CreateTodoOutcome
                }

                class CreateTodoInteractionImpl(
                    private val client: CreateTodo.Handler
                ) : CreateTodoInteraction {
                    override fun apply(body: CreateTodoRequest): CreateTodoInteraction.CreateTodoOutcome {
                        val request = CreateTodo.Request(body)
                        val response = client.createTodo(request)
                        return when (response) {
                            is CreateTodo.Response201 -> CreateTodoInteraction.CreateTodoResponse201(response.body)
                            is CreateTodo.Response400 -> CreateTodoInteraction.CreateTodoResponse400(response.body)
                        }
                    }
                }
                """;

        assertEquals(expected.strip(), result.strip());
    }

    @Test
    void emitEndpointWithQueryParams() {
        // GET /todos ? search: String, limit: Integer -> { 200 -> TodoDto[] }
        Endpoint endpoint = new Endpoint(
            null,
            List.of(),
            new DefinitionIdentifier("ListTodos"),
            Endpoint.Method.GET,
            List.of(new Endpoint.Segment.Literal("/todos")),
            List.of(
                new Field(
                    List.of(),
                    new FieldIdentifier("search"),
                    new Reference.Primitive(new Reference.Primitive.Type.String(null), false)
                ),
                new Field(
                    List.of(),
                    new FieldIdentifier("limit"),
                    new Reference.Primitive(
                        new Reference.Primitive.Type.Integer(Reference.Primitive.Type.Precision.P32, null),
                        false
                    )
                )
            ),
            List.of(), // headers
            List.of(new Endpoint.Request(null)),
            List.of(
                new Endpoint.Response(
                    "200",
                    List.of(),
                    new Endpoint.Content("application/json",
                        new Reference.Iterable(new Reference.Custom("TodoDto", false), false)),
                    List.of()
                )
            )
        );

        String result = emitter.emit(endpoint);

        String expected = """
                import com.ing.baker.recipe.javadsl.Interaction

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
                        val response = client.listTodos(request)
                        return when (response) {
                            is ListTodos.Response200 -> ListTodosInteraction.ListTodosResponse200(response.body)
                        }
                    }
                }
                """;

        assertEquals(expected.strip(), result.strip());
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec test -q`
Expected: FAIL — `emit(Endpoint)` returns empty string

- [ ] **Step 3: Implement `emit(Endpoint)` in `BakerKotlinEmitter`**

Replace the `emit(Endpoint)` method in `BakerKotlinEmitter.java` with:

```java
@NotNull
@Override
public String emit(@NotNull Endpoint endpoint) {
    String name = emit(endpoint.getIdentifier());
    String interactionName = name + "Interaction";
    String outcomeName = name + "Outcome";

    StringBuilder sb = new StringBuilder();

    // Import
    sb.append("import com.ing.baker.recipe.javadsl.Interaction\n\n");

    // Interface
    sb.append("interface ").append(interactionName).append(" : Interaction {\n");
    sb.append("    sealed interface ").append(outcomeName).append("\n");

    // Response events — one per status code
    for (Endpoint.Response response : endpoint.getResponses()) {
        String eventName = name + "Response" + response.getStatus();
        if (response.getContent() != null) {
            String bodyType = emitReference(response.getContent().getReference());
            sb.append("    data class ").append(eventName)
              .append("(val body: ").append(bodyType).append(") : ")
              .append(outcomeName).append("\n");
        } else {
            sb.append("    data object ").append(eventName).append(" : ")
              .append(outcomeName).append("\n");
        }
    }

    sb.append("\n");

    // apply() method — collect all input params
    List<String[]> params = collectParams(endpoint);
    String paramList = params.stream()
        .map(p -> p[0] + ": " + p[1])
        .collect(java.util.stream.Collectors.joining(", "));
    sb.append("    fun apply(").append(paramList).append("): ").append(outcomeName).append("\n");
    sb.append("}\n\n");

    // Implementation class
    String handlerMethod = Character.toLowerCase(name.charAt(0)) + name.substring(1);
    sb.append("class ").append(interactionName).append("Impl(\n");
    sb.append("    private val client: ").append(name).append(".Handler\n");
    sb.append(") : ").append(interactionName).append(" {\n");

    String argList = params.stream()
        .map(p -> p[0])
        .collect(java.util.stream.Collectors.joining(", "));

    sb.append("    override fun apply(").append(paramList).append("): ")
      .append(interactionName).append(".").append(outcomeName).append(" {\n");
    sb.append("        val request = ").append(name).append(".Request(").append(argList).append(")\n");
    sb.append("        val response = client.").append(handlerMethod).append("(request)\n");
    sb.append("        return when (response) {\n");

    for (Endpoint.Response response : endpoint.getResponses()) {
        String eventName = name + "Response" + response.getStatus();
        sb.append("            is ").append(name).append(".Response").append(response.getStatus())
          .append(" -> ").append(interactionName).append(".").append(eventName);
        if (response.getContent() != null) {
            sb.append("(response.body)");
        }
        sb.append("\n");
    }

    sb.append("        }\n");
    sb.append("    }\n");
    sb.append("}");

    return sb.toString();
}

/**
 * Collects all input parameters from path segments, query params, headers, and request body.
 * Returns list of [name, type] pairs.
 */
private java.util.List<String[]> collectParams(Endpoint endpoint) {
    java.util.List<String[]> params = new java.util.ArrayList<>();

    // Path parameters
    for (Endpoint.Segment segment : endpoint.getPath()) {
        if (segment instanceof Endpoint.Segment.Param param) {
            params.add(new String[]{
                param.getIdentifier().getValue(),
                emitReference(param.getReference())
            });
        }
    }

    // Query parameters
    for (Field query : endpoint.getQueries()) {
        params.add(new String[]{
            query.getIdentifier().getValue(),
            emitReference(query.getReference())
        });
    }

    // Header parameters
    for (Field header : endpoint.getHeaders()) {
        params.add(new String[]{
            header.getIdentifier().getValue(),
            emitReference(header.getReference())
        });
    }

    // Request body
    for (Endpoint.Request request : endpoint.getRequests()) {
        if (request.getContent() != null) {
            params.add(new String[]{
                "body",
                emitReference(request.getContent().getReference())
            });
        }
    }

    return params;
}
```

Also add these imports at the top of the file:

```java
import java.util.List;
import java.util.stream.Collectors;
```

And change the `emitReference` method from `private` to package-private (remove `private` modifier) so it can be reused.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec test -q`
Expected: PASS — all 3 tests green

- [ ] **Step 5: Commit**

```bash
git add baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitter.java
git add baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitterTest.java
git commit -m "feat: implement BakerKotlinEmitter endpoint-to-interaction generation"
```

---

### Task 4: Implement `BakerJavaEmitter` — scaffold with no-op methods

**Files:**
- Create: `baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerJavaEmitter.java`

- [ ] **Step 1: Create `BakerJavaEmitter.java`**

Same structure as `BakerKotlinEmitter` but targeting Java output. All methods return no-op except `emit(Identifier)` and `emit(Reference)`.

```java
package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.emit.LanguageEmitter;
import community.flock.wirespec.compiler.core.emit.FileExtension;
import community.flock.wirespec.compiler.core.emit.Shared;
import community.flock.wirespec.compiler.core.parse.ast.Channel;
import community.flock.wirespec.compiler.core.parse.ast.Endpoint;
import community.flock.wirespec.compiler.core.parse.ast.Enum;
import community.flock.wirespec.compiler.core.parse.ast.Field;
import community.flock.wirespec.compiler.core.parse.ast.Identifier;
import community.flock.wirespec.compiler.core.parse.ast.Module;
import community.flock.wirespec.compiler.core.parse.ast.Reference;
import community.flock.wirespec.compiler.core.parse.ast.Refined;
import community.flock.wirespec.compiler.core.parse.ast.Type;
import community.flock.wirespec.compiler.core.parse.ast.Union;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class BakerJavaEmitter extends LanguageEmitter {

    @NotNull
    @Override
    public String getSingleLineComment() {
        return "//";
    }

    @NotNull
    @Override
    public FileExtension getExtension() {
        return FileExtension.Java;
    }

    @Nullable
    @Override
    public Shared getShared() {
        return null;
    }

    @NotNull
    @Override
    public String notYetImplemented() {
        return "";
    }

    @NotNull
    @Override
    public String emit(@NotNull Identifier identifier) {
        return identifier.getValue();
    }

    @NotNull
    @Override
    public String emit(@NotNull Endpoint endpoint) {
        return ""; // implemented in Task 5
    }

    @NotNull
    @Override
    public String emit(@NotNull Type type, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Type.Shape shape) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Field field) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference reference) {
        return emitReference(reference);
    }

    @NotNull
    @Override
    public String emit(@NotNull Reference.Primitive.Type.Constraint constraint) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Enum anEnum, @NotNull Module module) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Union union) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emitValidator(@NotNull Refined refined) {
        return notYetImplemented();
    }

    @NotNull
    @Override
    public String emit(@NotNull Channel channel) {
        return notYetImplemented();
    }

    /**
     * Maps wirespec Reference types to Java type names.
     */
    String emitReference(Reference reference) {
        String typeName;
        if (reference instanceof Reference.Primitive primitive) {
            typeName = switch (primitive.getType()) {
                case Reference.Primitive.Type.String s -> "String";
                case Reference.Primitive.Type.Integer i -> switch (i.getPrecision()) {
                    case P32 -> "Integer";
                    case P64 -> "Long";
                };
                case Reference.Primitive.Type.Number n -> switch (n.getPrecision()) {
                    case P32 -> "Float";
                    case P64 -> "Double";
                };
                case Reference.Primitive.Type.Boolean b -> "Boolean";
                case Reference.Primitive.Type.Bytes b -> "byte[]";
                default -> "Object";
            };
        } else if (reference instanceof Reference.Custom custom) {
            typeName = custom.getValue();
        } else if (reference instanceof Reference.Iterable iterable) {
            typeName = "java.util.List<" + emitReference(iterable.getReference()) + ">";
        } else if (reference instanceof Reference.Dict dict) {
            typeName = "java.util.Map<String, " + emitReference(dict.getReference()) + ">";
        } else if (reference instanceof Reference.Unit u) {
            typeName = "Void";
        } else {
            typeName = "Object";
        }
        return typeName;
    }
}
```

- [ ] **Step 2: Verify it compiles**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec compile -q`
Expected: BUILD SUCCESS

- [ ] **Step 3: Commit**

```bash
git add baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerJavaEmitter.java
git commit -m "feat: add BakerJavaEmitter scaffold with type mapping"
```

---

### Task 5: Implement `BakerJavaEmitter.emit(Endpoint)` — Java interaction generation

**Files:**
- Modify: `baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerJavaEmitter.java`
- Create: `baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerJavaEmitterTest.java`

- [ ] **Step 1: Write the test**

```java
package com.ing.baker.recipe.wirespec;

import community.flock.wirespec.compiler.core.parse.ast.*;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class BakerJavaEmitterTest {

    private final BakerJavaEmitter emitter = new BakerJavaEmitter();

    @Test
    void emitSimpleGetEndpoint() {
        Endpoint endpoint = new Endpoint(
            null,
            List.of(),
            new DefinitionIdentifier("GetTodo"),
            Endpoint.Method.GET,
            List.of(
                new Endpoint.Segment.Literal("/todos/"),
                new Endpoint.Segment.Param(
                    new FieldIdentifier("id"),
                    new Reference.Primitive(
                        new Reference.Primitive.Type.Integer(Reference.Primitive.Type.Precision.P64, null),
                        false
                    )
                )
            ),
            List.of(),
            List.of(),
            List.of(new Endpoint.Request(null)),
            List.of(
                new Endpoint.Response(
                    "200",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("TodoDto", false)),
                    List.of()
                ),
                new Endpoint.Response(
                    "404",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("ErrorDto", false)),
                    List.of()
                )
            )
        );

        String result = emitter.emit(endpoint);

        String expected = """
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
                """;

        assertEquals(expected.strip(), result.strip());
    }

    @Test
    void emitPostEndpointWithBody() {
        Endpoint endpoint = new Endpoint(
            null,
            List.of(),
            new DefinitionIdentifier("CreateTodo"),
            Endpoint.Method.POST,
            List.of(new Endpoint.Segment.Literal("/todos")),
            List.of(),
            List.of(),
            List.of(new Endpoint.Request(
                new Endpoint.Content("application/json", new Reference.Custom("CreateTodoRequest", false))
            )),
            List.of(
                new Endpoint.Response(
                    "201",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("TodoDto", false)),
                    List.of()
                ),
                new Endpoint.Response(
                    "400",
                    List.of(),
                    new Endpoint.Content("application/json", new Reference.Custom("ErrorDto", false)),
                    List.of()
                )
            )
        );

        String result = emitter.emit(endpoint);

        String expected = """
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
                """;

        assertEquals(expected.strip(), result.strip());
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec test -q`
Expected: FAIL — Java emitter tests fail (Kotlin tests still pass)

- [ ] **Step 3: Implement `emit(Endpoint)` in `BakerJavaEmitter`**

Replace the `emit(Endpoint)` method in `BakerJavaEmitter.java` with:

```java
@NotNull
@Override
public String emit(@NotNull Endpoint endpoint) {
    String name = emit(endpoint.getIdentifier());
    String interactionName = name + "Interaction";
    String outcomeName = name + "Outcome";

    StringBuilder sb = new StringBuilder();

    // Imports
    sb.append("import com.ing.baker.recipe.javadsl.Interaction;\n");
    sb.append("import com.ing.baker.recipe.annotations.FiresEvent;\n\n");

    // Interface
    sb.append("public interface ").append(interactionName).append(" extends Interaction {\n");
    sb.append("    interface ").append(outcomeName).append(" {}\n");

    // Response event classes — one per status code
    for (Endpoint.Response response : endpoint.getResponses()) {
        String eventName = name + "Response" + response.getStatus();
        if (response.getContent() != null) {
            String bodyType = emitReference(response.getContent().getReference());
            sb.append("    class ").append(eventName).append(" implements ").append(outcomeName).append(" {\n");
            sb.append("        public final ").append(bodyType).append(" body;\n");
            sb.append("        public ").append(eventName).append("(").append(bodyType).append(" body) { this.body = body; }\n");
            sb.append("    }\n");
        } else {
            sb.append("    class ").append(eventName).append(" implements ").append(outcomeName).append(" {}\n");
        }
    }

    sb.append("\n");

    // @FiresEvent annotation
    String eventClasses = endpoint.getResponses().stream()
        .map(r -> name + "Response" + r.getStatus() + ".class")
        .collect(Collectors.joining(", "));
    sb.append("    @FiresEvent(oneOf = {").append(eventClasses).append("})\n");

    // apply() method
    List<String[]> params = collectParams(endpoint);
    String paramList = params.stream()
        .map(p -> p[1] + " " + p[0])
        .collect(Collectors.joining(", "));
    sb.append("    ").append(outcomeName).append(" apply(").append(paramList).append(");\n");
    sb.append("}");

    return sb.toString();
}

/**
 * Collects all input parameters from path segments, query params, headers, and request body.
 * Returns list of [name, type] pairs.
 */
private List<String[]> collectParams(Endpoint endpoint) {
    List<String[]> params = new ArrayList<>();

    // Path parameters
    for (Endpoint.Segment segment : endpoint.getPath()) {
        if (segment instanceof Endpoint.Segment.Param param) {
            params.add(new String[]{
                param.getIdentifier().getValue(),
                emitReference(param.getReference())
            });
        }
    }

    // Query parameters
    for (Field query : endpoint.getQueries()) {
        params.add(new String[]{
            query.getIdentifier().getValue(),
            emitReference(query.getReference())
        });
    }

    // Header parameters
    for (Field header : endpoint.getHeaders()) {
        params.add(new String[]{
            header.getIdentifier().getValue(),
            emitReference(header.getReference())
        });
    }

    // Request body
    for (Endpoint.Request request : endpoint.getRequests()) {
        if (request.getContent() != null) {
            params.add(new String[]{
                "body",
                emitReference(request.getContent().getReference())
            });
        }
    }

    return params;
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec test -q`
Expected: PASS — all tests green (both Kotlin and Java emitter tests)

- [ ] **Step 5: Commit**

```bash
git add baker-wirespec/src/main/java/com/ing/baker/recipe/wirespec/BakerJavaEmitter.java
git add baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerJavaEmitterTest.java
git commit -m "feat: implement BakerJavaEmitter endpoint-to-interaction generation"
```

---

### Task 6: Edge case — endpoint with no response body

**Files:**
- Modify: `baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitterTest.java`
- Modify: `baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerJavaEmitterTest.java`

- [ ] **Step 1: Add Kotlin test for no-body response**

Add to `BakerKotlinEmitterTest.java`:

```java
@Test
void emitEndpointWithNoBodyResponse() {
    // DELETE /todos/{id} -> { 204 -> Unit }
    Endpoint endpoint = new Endpoint(
        null,
        List.of(),
        new DefinitionIdentifier("DeleteTodo"),
        Endpoint.Method.DELETE,
        List.of(
            new Endpoint.Segment.Literal("/todos/"),
            new Endpoint.Segment.Param(
                new FieldIdentifier("id"),
                new Reference.Primitive(
                    new Reference.Primitive.Type.Integer(Reference.Primitive.Type.Precision.P64, null),
                    false
                )
            )
        ),
        List.of(),
        List.of(),
        List.of(new Endpoint.Request(null)),
        List.of(
            new Endpoint.Response("204", List.of(), null, List.of())
        )
    );

    String result = emitter.emit(endpoint);

    String expected = """
            import com.ing.baker.recipe.javadsl.Interaction

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
                    val response = client.deleteTodo(request)
                    return when (response) {
                        is DeleteTodo.Response204 -> DeleteTodoInteraction.DeleteTodoResponse204
                    }
                }
            }
            """;

    assertEquals(expected.strip(), result.strip());
}
```

- [ ] **Step 2: Add Java test for no-body response**

Add to `BakerJavaEmitterTest.java`:

```java
@Test
void emitEndpointWithNoBodyResponse() {
    Endpoint endpoint = new Endpoint(
        null,
        List.of(),
        new DefinitionIdentifier("DeleteTodo"),
        Endpoint.Method.DELETE,
        List.of(
            new Endpoint.Segment.Literal("/todos/"),
            new Endpoint.Segment.Param(
                new FieldIdentifier("id"),
                new Reference.Primitive(
                    new Reference.Primitive.Type.Integer(Reference.Primitive.Type.Precision.P64, null),
                    false
                )
            )
        ),
        List.of(),
        List.of(),
        List.of(new Endpoint.Request(null)),
        List.of(
            new Endpoint.Response("204", List.of(), null, List.of())
        )
    );

    String result = emitter.emit(endpoint);

    String expected = """
            import com.ing.baker.recipe.javadsl.Interaction;
            import com.ing.baker.recipe.annotations.FiresEvent;

            public interface DeleteTodoInteraction extends Interaction {
                interface DeleteTodoOutcome {}
                class DeleteTodoResponse204 implements DeleteTodoOutcome {}

                @FiresEvent(oneOf = {DeleteTodoResponse204.class})
                DeleteTodoOutcome apply(Long id);
            }
            """;

    assertEquals(expected.strip(), result.strip());
}
```

- [ ] **Step 3: Run tests**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec test -q`
Expected: PASS — if already handled by the null content check in Task 3/5. If not, fix the emitter logic and re-run.

- [ ] **Step 4: Commit**

```bash
git add baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerKotlinEmitterTest.java
git add baker-wirespec/src/test/java/com/ing/baker/recipe/wirespec/BakerJavaEmitterTest.java
git commit -m "test: add edge case tests for endpoints with no response body"
```

---

### Task 7: Final build verification

**Files:** None — verification only.

- [ ] **Step 1: Run full module build**

Run: `cd /Users/wilmveel/Projects/baker && mvn -pl baker-wirespec clean verify -q`
Expected: BUILD SUCCESS with all tests passing

- [ ] **Step 2: Verify the emitter classes are in the JAR**

Run: `jar tf baker-wirespec/target/baker-wirespec-5.1.0-SNAPSHOT.jar | grep -i baker`
Expected: Should list `com/ing/baker/recipe/wirespec/BakerKotlinEmitter.class` and `com/ing/baker/recipe/wirespec/BakerJavaEmitter.class`

- [ ] **Step 3: Commit any final fixes if needed**

Only if prior steps revealed issues.
