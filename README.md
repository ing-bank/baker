# BAKER

[![Build Status](https://api.travis-ci.org/ing-bank/baker.png?branch=master)](https://travis-ci.org/ing-bank/baker)
[![Maven Central](https://img.shields.io/maven-central/v/com.ing/baker_2.11.svg)](https://maven-badges.herokuapp.com/maven-central/com.ing/baker_2.11)
[![codecov.io](http://codecov.io/github/ing-bank/baker/coverage.svg?branch=master)](https://codecov.io/gh/ing-bank/baker?branch=master)

# Overview

Baker is a library that reduces the effort to orchestrate (micros)service-based process flows.
Developers declare the orchestration logic in a recipe.
A recipe is made out of interactions (system calls), ingredients (data) and events.
A visual representation (shown below) of the recipe allows product owners, architects and developers to talk the same language.


![](TestRecipe.png)


Baker consists of a DSL that allows developers to choose interactions from a catalogue and re-use them in their own recipes.
Developers can use Java or Scala as a programming language. Each recipe is turned into a [Petri net](https://www.wikiwand.com/en/Petri_net) at runtime.

Petri nets have two interesting mathematical properties that we’d like to explore in the near future:
- **reachability** – can we deliver on a promise (recipe) at all – this will allow developers to check during compile time if the recipe they’ve created makes sense and achieves the desired end state (fulfills the customer order);
- **liveliness** – do we have steps in a recipe that make no sense (unreachable, “dead” code) – this will allow developers to create lean and mean recipes (the less code you write, the less bugs you produce, the less you support);

## Getting Started

To get started with SBT, simply add the following to your build.sbt file:

```
libraryDependencies += "com.ing" %% "baker" % "0.2.21"
```

## How to contribute?

Execute the following commands in your terminal to get started with the development of BAKER.


```
$ git clone https://github.com/ing-bank/baker.git
$ cd Baker
$ sbt
$ compile
```

## How to visualize your recipe?
Baker can turn a recipe into a DOT representation which can then be visualized using the following web-site for example (http://www.webgraphviz.com).

Another way to visualize the recipe is to install [Graphviz](http://www.graphviz.org) on your development machine. On your Mac, install using [brew](https://brew.sh):

```
brew install graphviz
```
To test that all works fine, save the following text in a graph.dot file:
```
digraph d {  A [label="Hello"]  B [label="World"]  C [label="Everyone"]  A -> { B C } }
```
To create a PNG, run:
```
dot -v -Tpng -O graph.dot
```
Preview the results:
```
open graph.dot.png
```
You are all set to visualize your recipes now!

You can also use custom fonts, for more info see (http://www.graphviz.org/doc/fontfaq.txt).

## References
1. DOT Graph Description Language (https://en.wikipedia.org/wiki/DOT_(graph_description_language)) - explain more about the format Baker uses to product a graphical representation of the recipe;
2. Order fulfillment (https://en.wikipedia.org/wiki/Order_fulfillment) - gives an idea about the theory behind order fulfillment strategies. As you are in the business of producing and selling products to people, you are in the business of fulfillment;