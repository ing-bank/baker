# Getting started

## Project setup

Baker is released to [maven central](https://search.maven.org/search?q=com.ing.baker).

You can add following dependencies to your `maven` or `sbt` project to start using it:

``` scala tab="Sbt"
dependencies += "com.ing.baker" %% "baker-recipe-dsl" % "2.0.3"
dependencies += "com.ing.baker" %% "baker-compiler" % "2.0.3"
dependencies += "com.ing.baker" %% "baker-runtime" % "2.0.3"
```

``` maven tab="Maven"
<dependencies>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-recipe-dsl_2.12</artifactId>
   <version>2.0.3</version>
</dependencies>
<dependencies>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-compiler_2.12</artifactId>
   <version>2.0.3</version>
</dependencies>
<dependencies>
   <groupId>com.ing.baker</groupId>
   <artifactId>baker-runtime_2.12</artifactId>
   <version>2.0.3</version>
</dependencies>

```

This includes *ALL* baker modules to your project. If you only need partial functionality you can pick and choose the modules you need.

### Modules

An explanation of the baker modules.

| Module | Description |
| --- | --- |
| recipe-dsl | [DSL](recipe-dsl.md) to describe your recipes (process blueprints) *declaritively* |
| runtime | [Runtime](baker-runtime.md) based on [Akka](htts://www.akka.io) to manage and execute your recipes |
| compiler | [Compiles your recipe](baker-runtime.md#compiling-your-recipe) description into a model that the runtime can execute |
| intermediate-language | Recipe and Petri-net model that the runtime can execute |

This is the dependency graph between the modules.

![](../images/deps.svg)

## Continuing from here

After adding the dependencies you can continue to:

 - Familiarize yourself with the [concepts](concepts.md).
 - Immediately start [writing your recipes](recipe-dsl.md).