<div align="center">
<img src="https://github.com/ing-bank/baker/blob/master/baker-logo.png?raw=true" alt="Baker Logo">

[![Build Status](https://dev.azure.com/BakeryOSS/BakeryOSS/_apis/build/status/baker-oss-pr?branchName=master)](https://dev.azure.com/BakeryOSS/BakeryOSS/_build?definitionId=9&_a=summary)
[![Maven Central](https://img.shields.io/maven-central/v/com.ing.baker/baker-runtime_2.12.svg?label=Maven%20Central&logo=apachemaven)](https://search.maven.org/artifact/com.ing.baker/baker-runtime_2.12)
[![codecov.io](http://codecov.io/github/ing-bank/baker/coverage.svg?branch=master)](https://codecov.io/gh/ing-bank/baker?branch=master)
</div>

# Baker

Baker is a library that provides a simple and intuitive way to orchestrate microservice-based process flows.

You declare your orchestration logic as a recipe using the Java, Kotlin, or Scala DSL. A recipe consists of
`interactions` (system calls), `ingredients` (data), and `events`.

Bakers ability to visualize recipes provides a powerful communication tool that helps product owners, architects, and
engineers to have a common understanding of the business process. This feature allows you to easily share your recipe
with others, enabling collaboration and feedback.

Baker allows for the reuse of common interactions across different recipes, promoting consistency and reducing
duplication. With Baker, you can quickly assemble complex process flows by reusing pre-existing building blocks that
have been built by other teams within your company.

Use the list below to learn more about Baker:

- [Documentation](https://ing-bank.github.io/baker/)
    - [Concepts](https://ing-bank.github.io/baker/sections/concepts/): high level concepts and terminology
    - [Recipe DSL](https://ing-bank.github.io/baker/sections/reference/dsls/): how to use the recipe DSL
    - [Visualization](https://ing-bank.github.io/baker/sections/reference/visualization/): how to visualize a recipe
- [Baker Talk @ J-Fall 2021](https://www.youtube.com/watch?v=U4aCUT9zIFk): API orchestration taken to the next level

## A bird's-eye view of Baker

A recipe is the blueprint of your business process. To create this blueprint you use the Java, Kotlin, or Scala DSL. The
examples below demonstrate a recipe for a simple web shop process.

<details>
    <summary>Java DSL</summary>

```java
final Recipe recipe=new Recipe("Web shop")
        .withSensoryEvents(
        CustomerInfoReceived.class,
        OrderPlaced.class,
        PaymentMade.class
    )
            .withInteractions(
            InteractionDescriptor.of(ValidateOrder.class),
        InteractionDescriptor.of(ReserveItems.class)
        .withRequiredEvent(PaymentMade.class),
        InteractionDescriptor.of(ShipGoods.class),
        InteractionDescriptor.of(SendInvoice.class)
        .withRequiredEvent(GoodsShipped.class)
        )
        .withDefaultFailureStrategy(
        new RetryWithIncrementalBackoffBuilder()
        .withInitialDelay(Duration.ofMillis(100))
        .withDeadline(Duration.ofHours(24))
        .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
        .build());
```

</details>

<details>
    <summary>Kotlin DSL</summary>

```kotlin
val recipe = recipe("Web shop") {
    sensoryEvents {
        event<CustomerInfoReceived>()
        event<OrderPlaced>()
        event<PaymentMade>()
    }
    interaction<ValidateOrder>()
    interaction<ReserveItems> {
        requiredEvents {
            event<PaymentMade>()
        }
    }
    interaction<ShipGoods>()
    interaction<SendInvoice> {
        requiredEvents {
            event<GoodsShipped>()
        }
    }
    defaultFailureStrategy = retryWithIncrementalBackoff {
        initialDelay = 100.milliseconds
        until = deadline(24.hours)
        maxTimeBetweenRetries = 10.minutes
    }
}
```

</details>

<details>
    <summary>Scala DSL</summary>

```scala
val recipe: Recipe = Recipe("Web shop")
  .withSensoryEvents(
    Event[CustomerInfoReceived],
    Event[OrderPlaced],
    Event[PaymentMade]
  )
  .withInteractions(
    ValidateOrder,
    ReserveItems
      .withRequiredEvent(Event[PaymentMade])
      ShipGoods,
    SendInvoice
      .withRequiredEvent(goodsShipped)
  )
  .withDefaultFailureStrategy(
    RetryWithIncrementalBackoff
      .builder()
      .withInitialDelay(100 milliseconds)
      .withUntil(Some(UntilDeadline(24 hours)))
      .withMaxTimeBetweenRetries(Some(10 minutes))
      .build()
  )
```

</details>

<details>
    <summary>Visualization</summary>

Events are gray, ingredients orange, and interactions lilac:

![](docs/images/webshop.svg)

</details>

## Getting Started

Baker is released to [Maven Central](https://search.maven.org/search?q=g:com.ing.baker). To use Baker you need three
modules.

1. recipe-dsl: DSL to describe recipes in a declarative manner
2. compiler: Compiles recipes into models the runtime can execute
3. runtime: The runtime to manage and execute recipes

> **Note**
> If you want to use the Kotlin DSL add `baker-recipe-dsl-kotlin_2.13` instead of `baker-recipe-dsl_2.13`.

### Maven

```xml

<dependency>
    <groupId>com.ing.baker</groupId>
    <artifactId>baker-recipe-dsl_2.13</artifactId>
    <version>3.6.3</version>
</dependency>
<dependency>
    <groupId>com.ing.baker</groupId>
    <artifactId>baker-compiler_2.13</artifactId>
    <version>3.6.3</version>
</dependency>
<dependency>
    <groupId>com.ing.baker</groupId>
    <artifactId>baker-runtime_2.13</artifactId>
    <version>3.6.3</version>
</dependency>
```

### Gradle

```groovy
implementation 'com.ing.baker:baker-recipe-dsl_2.13:3.6.3'
implementation 'com.ing.baker:baker-compiler_2.13:3.6.3'
implementation 'com.ing.baker:baker-runtime_2.13:3.6.3'
```

### Scala SBT

Baker gets cross compiled and released for both Scala 2.12 and 2.13.

```scala
libraryDependencies += "com.ing.baker" % "baker-recipe-dsl_2.13" % "3.6.3"
libraryDependencies += "com.ing.baker" % "baker-compiler_2.13" % "3.6.3"
libraryDependencies += "com.ing.baker" % "baker-runtime_2.13" % "3.6.3"
```

## Contributing

We welcome your contributions! The simplest way to contribute to Baker is by creating a branch from a fork. You can then
create a pull request on GitHub from your branch.

### Compile and test

To compile and test all libraries:

```bash
sbt 
> compile
> test
```

To cross compile all libraries for Scala 2.12 and 2.13:

```bash
sbt
> +compile
> +test
```

### Compile or test a single project

To build a single project (baker-akka-runtime, baker-anotations, etc...):

1. Find the name of the project by running:

```bash
sbt 
> projects
```

2. Open the desired project via `sbt`:

```bash
sbt
> project <PROJECT_NAME>
> compile
> test
```
