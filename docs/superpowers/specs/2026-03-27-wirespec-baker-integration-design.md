# Wirespec-Baker Integration Design

## Overview

A custom wirespec emitter module (`baker-wirespec`) that generates Baker Interaction interfaces and implementations from wirespec endpoint definitions. Each API endpoint maps 1:1 to a Baker Interaction, enabling type-safe API consumption within Baker recipes.

## Architecture

### Approach

A new Maven module in the baker repo containing custom wirespec emitters. These plug into wirespec's existing Maven plugin via the `emitterClass` configuration — no custom Maven plugin needed.

### Module Structure

```
baker-wirespec/
├── pom.xml
└── src/main/java/com/ing/baker/recipe/wirespec/
    ├── BakerKotlinEmitter.java      # Kotlin interaction emitter
    └── BakerJavaEmitter.java        # Java interaction emitter
```

### Emitter Classes

| Class | Extends | File Extension | Output |
|-------|---------|----------------|--------|
| `BakerKotlinEmitter` | `LanguageEmitter` | `.kt` | Kotlin interaction interfaces + implementations |
| `BakerJavaEmitter` | `LanguageEmitter` | `.java` | Java interaction interfaces + implementations |

Both emitters only process `Endpoint` AST nodes. `Type`, `Enum`, `Refined`, `Union`, and `Channel` return no-op — those are handled by wirespec's standard emitters.

## Endpoint-to-Interaction Mapping

### Input (wirespec)

```wirespec
type TodoDto {
  id: Integer,
  name: String
}

type ErrorDto {
  message: String
}

endpoint GetTodo GET /todos/{id: Integer} -> {
  200 -> TodoDto
  404 -> ErrorDto
}

endpoint CreateTodo POST /todos RequestBody -> {
  201 -> TodoDto
  400 -> ErrorDto
}
```

### Mapping Rules

- **Endpoint name** → `{EndpointName}Interaction` (interface extending `Interaction`)
- **Response per status code** → `{EndpointName}Response{StatusCode}` (event class with response body field)
- **Sealed outcome** → `{EndpointName}Outcome` (sealed interface grouping all response events)
- **Path params, query params, headers** → flat `apply()` parameters (become Baker ingredients)
- **Request body** → additional `apply()` parameter

### Kotlin Output

#### Interface

```kotlin
package com.example.generated

import com.ing.baker.recipe.javadsl.Interaction

interface GetTodoInteraction : Interaction {
    sealed interface GetTodoOutcome
    data class GetTodoResponse200(val body: TodoDto) : GetTodoOutcome
    data class GetTodoResponse404(val body: ErrorDto) : GetTodoOutcome

    fun apply(id: Integer): GetTodoOutcome
}

interface CreateTodoInteraction : Interaction {
    sealed interface CreateTodoOutcome
    data class CreateTodoResponse201(val body: TodoDto) : CreateTodoOutcome
    data class CreateTodoResponse400(val body: ErrorDto) : CreateTodoOutcome

    fun apply(requestBody: RequestBody): CreateTodoOutcome
}
```

#### Implementation

```kotlin
package com.example.generated

class GetTodoInteractionImpl(
    private val client: Wirespec.Client<GetTodoEndpoint.Request, GetTodoEndpoint.Response>
) : GetTodoInteraction {

    override fun apply(id: Integer): GetTodoInteraction.GetTodoOutcome {
        val request = GetTodoEndpoint.Request(id)
        val response = client.invoke(request)
        return when (response) {
            is GetTodoEndpoint.Response200 -> GetTodoInteraction.GetTodoResponse200(response.body)
            is GetTodoEndpoint.Response404 -> GetTodoInteraction.GetTodoResponse404(response.body)
        }
    }
}
```

### Java Output

#### Interface

```java
package com.example.generated;

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
    GetTodoOutcome apply(Integer id);
}
```

#### Implementation

Same pattern as Kotlin — bridges wirespec's generated endpoint client to the Baker interaction interface.

## Dependencies

### baker-wirespec pom.xml

```xml
<dependencies>
    <!-- Wirespec compiler core — LanguageEmitter, AST nodes -->
    <dependency>
        <groupId>community.flock.wirespec</groupId>
        <artifactId>wirespec-compiler-core-jvm</artifactId>
        <version>${wirespec.version}</version>
    </dependency>

    <!-- Baker recipe DSL — Interaction trait (provided, referenced in generated code) -->
    <dependency>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker-recipe-dsl_2.13</artifactId>
        <version>${project.version}</version>
        <scope>provided</scope>
    </dependency>

    <!-- Baker annotations — @FiresEvent for Java emitter (provided) -->
    <dependency>
        <groupId>com.ing.baker</groupId>
        <artifactId>baker-annotations_2.13</artifactId>
        <version>${project.version}</version>
        <scope>provided</scope>
    </dependency>
</dependencies>
```

## Consumer Integration

### Maven Plugin Configuration

```xml
<plugin>
    <groupId>community.flock.wirespec.plugin.maven</groupId>
    <artifactId>wirespec-maven-plugin</artifactId>
    <version>${wirespec.version}</version>
    <executions>
        <!-- Standard Kotlin emitter for types + endpoint classes -->
        <execution>
            <id>wirespec-kotlin</id>
            <goals><goal>compile</goal></goals>
            <configuration>
                <input>${project.basedir}/src/main/wirespec</input>
                <output>${project.build.directory}/generated-sources/wirespec</output>
                <languages><language>Kotlin</language></languages>
                <packageName>com.example.generated</packageName>
            </configuration>
        </execution>
        <!-- Baker emitter for interaction interfaces + implementations -->
        <execution>
            <id>wirespec-baker</id>
            <goals><goal>compile</goal></goals>
            <configuration>
                <input>${project.basedir}/src/main/wirespec</input>
                <output>${project.build.directory}/generated-sources/wirespec</output>
                <emitterClass>com.ing.baker.recipe.wirespec.BakerKotlinEmitter</emitterClass>
                <packageName>com.example.generated</packageName>
            </configuration>
        </execution>
    </executions>
    <dependencies>
        <dependency>
            <groupId>com.ing.baker</groupId>
            <artifactId>baker-wirespec</artifactId>
            <version>${baker.version}</version>
        </dependency>
    </dependencies>
</plugin>
```

### Using in a Recipe

```kotlin
@ExperimentalDsl
val recipe = recipe("todo-recipe") {
    sensoryEvents {
        event<TodoRequested>()
    }
    interaction<GetTodoInteraction>()
    interaction<CreateTodoInteraction> {
        requiredEvents {
            event<GetTodoResponse404>()
        }
    }
}
```

### Wiring at Runtime

```kotlin
val wirespecClient: Wirespec.Client<...> = // user provides HTTP client
val baker = AkkaBaker.localDefault(actorSystem)

baker.addInteractionInstance(GetTodoInteractionImpl(wirespecClient))
baker.addInteractionInstance(CreateTodoInteractionImpl(wirespecClient))
```

## Compilation Pipeline

1. Wirespec Maven plugin discovers `.ws` files in `src/main/wirespec`
2. Standard emitter (Kotlin/Java) generates: types (`TodoDto`, `ErrorDto`), endpoint classes (`GetTodoEndpoint` with `Request`, `Response`, `Client`, `Server`)
3. Baker emitter generates: interaction interfaces (`GetTodoInteraction`) + implementations (`GetTodoInteractionImpl`) that bridge to the wirespec endpoint classes
4. All generated sources land in `target/generated-sources/wirespec`
5. Consumer code references interactions in recipes and wires implementations at runtime

## Testing

Unit tests feed wirespec AST nodes into the emitters and assert:
- Generated code string matches expected output
- Interaction interfaces follow Baker conventions (sealed outcome, `apply` method, `Interaction` trait)
- Implementation classes correctly bridge wirespec endpoint types to Baker outcome events

## Scope

### In scope
- `BakerKotlinEmitter` — generates Kotlin interaction interfaces + implementations
- `BakerJavaEmitter` — generates Java interaction interfaces + implementations
- Unit tests for both emitters
- Maven module configuration

### Out of scope
- Custom Maven plugin (use wirespec's existing plugin)
- Type/Enum/Refined/Union/Channel emission (handled by standard wirespec emitters)
- HTTP client implementation (user provides via wirespec's `Wirespec.Client`)
