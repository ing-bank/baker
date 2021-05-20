# BAKER

[![Build Status](https://api.travis-ci.org/ing-bank/baker.png?branch=master)](https://travis-ci.org/ing-bank/baker)
[![Maven Central](https://img.shields.io/maven-metadata/v/http/central.maven.org/maven2/com/ing/baker/baker-runtime_2.12/maven-metadata.xml.svg)](https://maven-badges.herokuapp.com/maven-central/com.ing.baker/baker-runtime_2.12)
[![codecov.io](http://codecov.io/github/ing-bank/baker/coverage.svg?branch=master)](https://codecov.io/gh/ing-bank/baker?branch=master)

![](baker-logo.png)

# Overview

Baker is a library that reduces the effort to orchestrate (micro)service-based process flows.
Developers declare the orchestration logic in a recipe.
A recipe is made out of **interactions** (system calls), **ingredients** (data) and **events**.
A visual representation (shown below) of the recipe allows product owners, architects and developers to talk the same language.

The official documentation website of Baker: [Official Documentation](https://ing-bank.github.io/baker/).

An introductory presentation of Baker: [Baker talk @ Amsterdam.Scala meetup](https://www.slideshare.net/BekirOguz/designing-process-flows-with-baker).

A talk about Baker at the Scale By the Bay 2017 conference: [Declare, verify and execute microservices-based process flows](https://www.youtube.com/watch?v=0bWQwUmeXHU).

For an example web-shop recipe in Scala, see the [examples sub-project](examples/baker-example/src/main/scala/webshop/webservice).
Java developers new to Baker can use this [workshop](https://github.com/nikolakasev/workshop-baker) to get familiar with the library by reading the workshop assignment PDF document and making the unit tests green.

WebShop Recipe:
```scala
  val webShopRecipe: Recipe =
    Recipe("WebShop")
      .withInteractions(
        validateOrder,
        manufactureGoods
          .withRequiredEvents(valid, paymentMade),
        shipGoods,
        sendInvoice
          .withRequiredEvent(goodsShipped)
      )
      .withSensoryEvents(
        customerInfoReceived,
        orderPlaced,
        paymentMade)
```
A visual representation of the WebShop recipe looks like the following, where the events are colored in gray, ingredients in orange and interactions in lilac:

![](docs/images/webshop.svg)


Baker consists of a DSL that allows developers to choose interactions from a catalogue and re-use them in their own recipes.
Developers can use Java or Scala as a programming language. 

# A Catalogue of Reusable Interactions
Let's look at three different products that a bank would sell to customers:

Checking Account | Savings Account | Customer Onboarding
--- | --- | ---
Verify Person's Identity | Verify Person's Identity | Verify Person's Identity
Register Person | Register Person | Register Person
Open *Checking* Account | Open *Savings* Account | `n/a`
Issue Debit Card | `n/a` | `n/a`
Send Message | Send Message | Send Message
Register Product Possession | Register Product Possession | `n/a`

As you can see, there are similarities in the products.

It becomes interesting when you're able to combine the same interactions in different recipes. New functionality can then be built quickly by re-using what's already available.

# How to apply Baker?
Applying Baker will only be successful if you make sure that:
1. You've compared the products your company is selling and there are similarities;
2. You've defined a catalogue of those capabilities necessary to deliver the products from;
3. Each capability (**interaction** in Baker terms) is accessible via an API of any sort (could be a micro-service, web-service, so on);

# Getting Started

To get started with SBT, simply add the following to your build.sbt file:

```
libraryDependencies += "com.ing.baker" %% "baker-recipe-dsl" % "3.0.3"
libraryDependencies += "com.ing.baker" %% "baker-runtime" % "3.0.3"
libraryDependencies += "com.ing.baker" %% "baker-compiler" % "3.0.3"
```

From 1.3.x to 2.0.x we cross compile to both Scala 2.11 and 2.12. 

Earlier releases are only available for Scala 2.11.

From 3.0.x we support only Scala 2.12.

# How to contribute?

Execute the following commands in your terminal to get started with the development of Baker:

```
$ git clone https://github.com/ing-bank/baker.git
$ cd baker
$ sbt
> compile
> test
```

# How to visualize your recipe?
Baker can turn a recipe into a DOT representation. It can then be visualized using the following web-site (http://www.webgraphviz.com).

Another way to visualize the recipe is to install [Graphviz](http://www.graphviz.org) on your development machine. On your Mac, install using [brew](https://brew.sh):

```
brew install graphviz
```

To test that all works fine, save the following text in a graph.dot file:

```
digraph d {
A [label="Hello"]
B [label="World"]
C [label="Everyone"]
A -> { B C }
}
```

Assuming you have the graphviz `dot` command you can create an SVG by running:

```
dot -v -Tsvg -O graph.dot
```

Alternatively you can use [graphviz-java](https://github.com/nidi3/graphviz-java) to generate the SVG in your code:

```scala
import guru.nidi.graphviz.engine.{Format, Graphviz}
import guru.nidi.graphviz.parse.Parser

val g = Parser.read(getRecipeVisualization)
Graphviz.fromGraph(g).render(Format.SVG).toString
```


Preview the results:

```
open graph.dot.svg
```

You are all set to visualize your recipes now!

To use custom fonts, see <http://www.graphviz.org/doc/fontfaq.txt>.

# References
1. DOT Graph Description Language (https://en.wikipedia.org/wiki/DOT_(graph_description_language)) - explains more about the format Baker uses to produce a graphical representation of the recipe;
2. Order fulfillment (https://en.wikipedia.org/wiki/Order_fulfillment) - gives an idea about the theory behind order fulfillment strategies. As you are in the business of producing and selling products to people, you are in the business of fulfillment;

# Security
Baker uses free open-source license from [Xanitizer](https://www.xanitizer.com/xanitizer) for code security scans.
