# Quick start guide

Add the following dependencies to your project. You can find the latest stable version on
[Maven Central](https://mvnrepository.com/artifact/com.ing.baker).

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

=== "Gradle"

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

    If you want to use the Kotlin DSL add `baker-recipe-dsl-kotlin_2.13` instead of `baker-recipe-dsl_2.13`.

### Modules

An explanation of the baker modules.

| Module | Description |
| --- | --- |
| recipe-dsl | [DSL](../reference/dsls) to describe your recipes (process blueprints) *declaritively* |
| runtime | [Runtime](../reference/runtime/) based on [akka](https://www.akka.io) to manage and execute your recipes |
| compiler | [Compiles your recipe](../reference/runtime/#recipecompilercompilerecipe) description into a model that the runtime can execute |
| intermediate-language | Recipe and Petri Net model that the runtime can execute |

This is the dependency graph between the modules.

![](../images/module-dependencies.svg)

## Continuing from here

After adding the dependencies you can continue to:

1. Understand the [high level concepts](../concepts).
2. If you like learning by doing, go through the [development life cycle section](../development-life-cycle/design-a-recipe).
3. If you like learning by description, go through the [reference section](../reference/main-abstractions).
