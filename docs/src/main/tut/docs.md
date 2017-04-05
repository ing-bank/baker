---
layout: docs
---

# Introduction

Fetch is a library that allows your to bake your process in a modular and declaritive
manner.

Developers declare the orchestration logic in a recipe.
A recipe is made out of system interactions, ingredients (data) and events.
A visual representation of the recipe allows product owners, architects and developers to talk the same language.


Baker consists of a DSL that allows developers to choose interactions from a catalogue and re-use them in their own recipes.
Developers can use Java or Scala as a programming language. Each recipe is turned into a petri net at runtime.

Petri-nets have two interesting mathematical properties that we’d like to explore in the near future:
- **reachability** – can we deliver on a promise (recipe) at all – this will allow developers to check during compile time if the recipe they’ve created makes sense and achieves the desired end state (fulfills the customer order);
- **liveliness** – do we have steps in a recipe that make no sense (unreachable, “dead” code) – this will allow developers to create lean and mean recipes (the less code you write, the less bugs you produce, the less you support);


Oftentimes, our applications read and manipulate data from a variety of
different sources such as databases, web services or file systems. These data
sources are subject to latency, and we'd prefer to query them efficiently.

If we are just reading data, we can make a series of optimizations such as:

 - batching requests to the same data source
 - requesting independent data from different sources in parallel
 - caching previously seen results

However, if we mix these optimizations with the code that fetches the data
we may end up trading clarity for performance. Furthermore, we are
mixing low-level (optimization) and high-level (business logic with the data
we read) concerns.


# How to contribute?

Execute the following commands in your terminal to get started with the development of BAKER.


```
$ git clone ssh://git@gitlab.ing.net:2222/Rocket/Baker.git
$ cd Baker
$ sbt
$ compile
```



# Installation

To begin, add the following dependency to your SBT build file:

```scala
"com.fortysevendeg" %% "fetch" % "0.5.0"
```

Or, if using Scala.js:

```scala
"com.fortysevendeg" %%% "fetch" % "0.5.0"
```


## Alternatives


# Usage

## Writing your first Recipe


# Resources

# Acknowledgements
