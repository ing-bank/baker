[![Build Status](https://api.travis-ci.org/ing-bank/baker.png?branch=master)](https://travis-ci.org/ing-bank/baker)
[![Maven Central](https://img.shields.io/maven-central/v/com.ing/baker_2.11.svg)](https://maven-badges.herokuapp.com/maven-central/com.ing/baker_2.11)
[![codecov.io](http://codecov.io/github/ing-bank/baker/coverage.svg?branch=master)](https://codecov.io/gh/ing-bank/baker?branch=master)




# BAKER

Baker is a library that reduces the effort to orchestrate (micros)service-based process flows.
Developers declare the orchestration logic in a recipe.
A recipe is made out of system interactions, ingredients (data) and events.
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


## Usage

TBD

## Dependencies


TBD
