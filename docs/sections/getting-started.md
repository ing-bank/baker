# Getting Started

## Project setup

Baker is released to [maven central](https://search.maven.org/search?q=com.ing.baker).

You can add following dependencies to your `maven` or `sbt` project to start using it:

=== "Sbt"

```scala 
dependencies += "com.ing.baker" %% "baker-recipe-dsl" % "3.0.0"
dependencies += "com.ing.baker" %% "baker-compiler" % "3.0.0"
dependencies += "com.ing.baker" %% "baker-runtime" % "3.0.0"
```

=== "Maven"

```xml 
<dependency>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-recipe-dsl_2.12</artifactId>
   <version>3.0.0</version>
</dependency>
<dependency>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-compiler_2.12</artifactId>
   <version>3.0.0</version>
</dependency>
<dependency>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-runtime_2.12</artifactId>
   <version>3.0.0</version>
</dependency>

```

This includes *ALL* baker modules to your project. If you only need partial functionality you can pick and choose the modules you need.

### Modules

An explanation of the baker modules.

| Module | Description |
| --- | --- |
| recipe-dsl | [DSL](../reference/dsls) to describe your recipes (process blueprints) *declaritively* |
| runtime | [Runtime](../reference/runtime/) based on [akka](https://www.akka.io) to manage and execute your recipes |
| compiler | [Compiles your recipe](../reference/runtime/#recipecompilercompilerecipe) description into a model that the runtime can execute |
| intermediate-language | Recipe and Petri Net model that the runtime can execute |

This is the dependency graph between the modules.

![](../images/deps.svg)

## Continuing from here

After adding the dependencies you can continue to:

1. Understand the [high level concepts](../concepts).
2. If you like learning by doing, go through the [development life cycle section](../development-life-cycle/design-a-recipe).
3. If you like learning by description, go through the [reference section](../reference/main-abstractions).
