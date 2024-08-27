# Quickstart guide

## Enable Maven Central repository

Baker is published in [Maven Central](https://mvnrepository.com/artifact/com.ing.baker). So you will need to enable
Maven Central repository as a source of dependencies in your build.

=== "Maven"

    ```
    Maven includes the Maven Central repository by default.
    ```

=== "Gradle (Kotlin)"

    ```kotlin
    repositories {
        mavenCentral()
    }
    ```

=== "Gradle (Groovy)"

    ```groovy
    repositories {
        mavenCentral()
    }
    ```

=== "Sbt"

    ```
    Most of the time Sbt includes the Maven Central repository by default.
    ```

## Include dependencies

Baker is composed of different modules. For most projects you need to include the three dependencies listed below.
If you don't require all functionality, simply select the ones you need for your project.

=== "Maven"

    ```xml 
    <dependency>
       <groupId>com.ing.baker</groupId>
       <artifactId>baker-recipe-dsl_2.13</artifactId>
       <version>${baker.version}</version>
    </dependency>
    <dependency>
       <groupId>com.ing.baker</groupId>
       <artifactId>baker-compiler_2.13</artifactId>
       <version>${baker.version}</version>
    </dependency>
    <dependency>
       <groupId>com.ing.baker</groupId>
       <artifactId>baker-runtime_2.13</artifactId>
       <version>${baker.version}</version>
    </dependency>
    ```

=== "Gradle (Kotlin)"

    ```kotlin
    implementation("com.ing.baker:baker-recipe-dsl-kotlin_2.13:$bakerVersion")
    implementation("com.ing.baker:baker-compiler_2.13:$bakerVersion")
    implementation("com.ing.baker:baker-runtime_2.13:$bakerVersion")
    ```

=== "Gradle (Groovy)"

    ```groovy
    implementation 'com.ing.baker:baker-recipe-dsl_2.13:$bakerVersion'
    implementation 'com.ing.baker:baker-compiler_2.13:$bakerVersion'
    implementation 'com.ing.baker:baker-runtime_2.13:$bakerVersion'
    ```

=== "Sbt"

    ```scala 
    dependencies += "com.ing.baker" %% "baker-recipe-dsl" % bakerVersion
    dependencies += "com.ing.baker" %% "baker-compiler" % bakerVersion
    dependencies += "com.ing.baker" %% "baker-runtime" % bakerVersion
    ```

!!! note

    Kotlin users should include `baker-recipe-dsl-kotlin_2.13` instead of `baker-recipe-dsl_2.13`.

!!! note

    Replace the version placeholders with the actual version you want to use. The latest stable version can be 
    found on [Maven Central](https://mvnrepository.com/artifact/com.ing.baker).

## Module overview

| Module                | Description                                                                                                |
|-----------------------|------------------------------------------------------------------------------------------------------------|
| recipe-dsl            | A declarative DSL to describe your recipes.                                                                |
| runtime               | The Baker runtime to manage and execute your recipes.                                                      |
| compiler              | A compiler that compiles recipes into a model that the runtime can execute.                                |
| intermediate-language | Recipe and Petri Net model used by the compiler and runtime. You don't interact with this module directly. |

## Dependency graph

![Dependency graph](../images/module-dependencies.svg)
