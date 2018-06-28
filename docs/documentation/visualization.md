# Visualization

## Generate a .dot representation

Baker can turn a recipe into a .dot representation. `.dot` is a notation for representing graphs.

``` scala
val recipe = RecipeCompiler.compileRecipe(Examples.webshop.webShopRecipe)

println(recipe.getRecipeVisualization)

```

This should output something like this:

```
digraph d {
  A [label="Hello"]
  B [label="World"]
  C [label="Everyone"]
  A -> { B C }
}
```

## Visualize

### Online

You can copy the .dot output and use the [webgraphviz.com](http://www.webgraphviz.com) to visualize it.

### Local

To generate an image locally you require the `graphviz` tool. See [graphviz.org](https://www.graphviz.org/) on how to
install it. On mac you can use `brew`.

```
brew install graphviz
```

Using the `dot` command you can then create an SVG by running:

```
dot -v -Tsvg -O graph.dot
```

### In application

Alternatively you can use [graphviz-java](https://github.com/nidi3/graphviz-java) to generate the SVG in your code:

``` scala
import guru.nidi.graphviz.engine.{Format, Graphviz}
import guru.nidi.graphviz.parse.Parser

val g = Parser.read(recipe.getRecipeVisualization)
Graphviz.fromGraph(g).render(Format.SVG).toString
```