# Visualization

## Generate a .DOT representation

Baker can turn a recipe into a DOT representation.

``` scala tab="Scala"
val recipe = RecipeCompiler.compileRecipe(Examples.webshop.webShopRecipe)

println(recipe.getRecipeVisualization)
```

``` java tab="Java"
final CompiledRecipe recipe = RecipeCompiler.compileRecipe(Examples.webshop.webShopRecipe);

System.out.println(recipe.getRecipeVisualization);
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

### Style customization

It is possible to define a custom visual style for your recipes.

To do so you need to add some configuration in your `application.conf`:

```
baker.visualization {
  style = "custom"
  styles.custom = {
     // place your style attributes here
  }
}

```

Please see the `default` theme in the [reference.conf](https://raw.githubusercontent.com/ing-bank/baker/master/recipe-dsl/src/main/resources/reference.conf)
as an example.

For an overview on what is possible to configure check out the [graphviz](https://www.graphviz.org/) documentation.

The only limitation we place is the `shape` attribute, which is hard coded for all elements in the graph.
We do this to garuantee some common visual base for all recipes.

## Visualize

Once you have a `.dot` representation there are various methods to visualize this.

### Online

You can copy the .dot output and use the [webgraphviz.com](http://www.webgraphviz.com).

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