# Recipe Visualization

Here we explain how to create a visual representation of your recipe like [this one](../index.md#visual-representation)

## Generate a .dot representation

Baker can turn a recipe into a .dot representation. `.dot` is a notation for representing graphs.

``` scala tab="Scala"
val recipe = RecipeCompiler.compileRecipe(Examples.webshop.webShopRecipe)

println(recipe.getRecipeVisualization)
```

``` java tab="Java"
final CompiledRecipe recipe = RecipeCompiler.compileRecipe(Examples.webshop.webShopRecipe);

System.out.println(recipe.getRecipeVisualization());
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

Once you have a `.dot` representation there are a few methods to visualize this.

### Online

You can copy the `.dot` string and use [webgraphviz.com](http://www.webgraphviz.com).

### Local

To generate an image locally you require the `graphviz` tool. See [graphviz.org](https://www.graphviz.org/) on how to
install it. On mac you can use `brew`.

```
brew install graphviz
```

Once installed the `dot` command can be used to create an SVG by running:

```
dot -v -Tsvg -O graph.dot
```

### In application

Alternatively you can use [graphviz-java](https://github.com/nidi3/graphviz-java) to generate the SVG in your code:

``` scala tab="Scala"
import guru.nidi.graphviz.engine.{Format, Graphviz}
import guru.nidi.graphviz.parse.Parser

val graph = Parser.read(recipe.getRecipeVisualization)
Graphviz.fromGraph(graph).render(Format.SVG).toString
```

``` java tab="Java"
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.parse.Parser;
import guru.nidi.graphviz.model.MutableGraph;

MutableGraph graph = Parser.read(recipe.getRecipeVisualization);
Graphviz.fromGraph(graph).render(Format.SVG).toString;
```

## Style customization

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

Please see the `default` theme in the [reference.conf](https://raw.githubusercontent.com/ing-bank/baker/master/intermediate-language/src/main/resources/reference.conf)
as an example.

For an overview on what is possible to configure check out the [graphviz](https://www.graphviz.org/) documentation.

It is not possible to alter the `shape` attribute, it is hard coded (fixed) for all elements in the graph.

This is done to garuantee a common visual language for all recipes.