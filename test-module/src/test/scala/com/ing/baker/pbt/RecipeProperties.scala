package com.ing.baker.pbt

import java.io.{File, PrintWriter}

import com.ing.baker.compiler.{RecipeCompiler, Sha256Hashing}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionOutput, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, Recipe}
import org.scalacheck.Prop.forAll
import org.scalacheck.{Gen, Properties}

class RecipeProperties extends Properties("Properties of a Recipe") {

  import RecipeProperties._

  property("baker compiler uses a (good enough) consistent hash algorithm") = forAll {
    (s1: String, s2: String) =>
      if (s1 != s2) Sha256Hashing.hashCode(s1) != Sha256Hashing.hashCode(s2)
      else Sha256Hashing.hashCode(s1) == Sha256Hashing.hashCode(s2)
  }

  property("baker can compile any small or huge recipe") = forAll(recipeGen) { recipe =>

    logRecipeStats(recipe)

    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    logCompiledRecipeStats(compiledRecipe)

    if (compiledRecipe.validationErrors.nonEmpty) {
      println(s"Validation errors: ${compiledRecipe.validationErrors}")
      dumpVisualRecipe(recipeVisualizationOutputPath, compiledRecipe)
    }

    compiledRecipe.validationErrors.isEmpty
  }

}

object RecipeProperties {

  // where to output the .dot files of the generated recipe visualizations
  val recipeVisualizationOutputPath: String = System.getProperty("java.io.tmpdir")

  val ingredientGen: Gen[Ingredient[_]] = for (name <- Gen.uuid) yield Ingredient[String](s"ingredient-$name")

  val eventGen: Gen[Event] = for {
    name <- Gen.uuid
    //    ingredients <- Gen.listOf(ingredientGen)
    nrOfIngredients <- Gen.choose(0, 10)
    ingredients <- Gen.listOfN(nrOfIngredients, ingredientGen)
  } yield Event(s"event-$name", ingredients)

  val interactionOutputGen: Gen[InteractionOutput] = for {
  //    events <- Gen.listOf(eventGen)
    nrOfEvents <- Gen.choose(0, 10)
    events <- Gen.listOfN(nrOfEvents, eventGen)
    ingredient <- ingredientGen
    output <- Gen.oneOf(ProvidesNothing(), FiresOneOfEvents(events), ProvidesIngredient(ingredient))
  } yield output

  def interactionGen(ingredients: Seq[common.Ingredient]): Gen[Interaction] = for {
    name <- Gen.uuid
    output <- interactionOutputGen
  } yield Interaction(s"interaction-$name", ingredients, output)

  def interactionDescriptorGen(ingredients: Seq[common.Ingredient]): Gen[InteractionDescriptor] = for {
    interaction <- interactionGen(ingredients)
  } yield InteractionDescriptor(interaction)

  val recipeGen: Gen[Recipe] = for {
    name <- Gen.uuid
    //    sensoryEvents <- Gen.listOf(eventGen)
    nrOfSensoryEvents <- Gen.choose(0, 100)
    sensoryEvents <- Gen.listOfN(nrOfSensoryEvents, eventGen)
    allProvidedIngredients = sensoryEvents.flatMap(_.providedIngredients)
    inputIngredients <- Gen.someOf(allProvidedIngredients) if inputIngredients.nonEmpty
    interactionDescriptors <- Gen.listOf(interactionDescriptorGen(inputIngredients))
  } yield Recipe(s"recipe-$name")
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactionDescriptors: _*)

  def dumpVisualRecipe(dumpDir: String, compiledRecipe: CompiledRecipe): Unit = {
    val fileName =
      if (dumpDir endsWith "/") s"$dumpDir${compiledRecipe.name}.dot"
      else s"$dumpDir/${compiledRecipe.name}.dot"

    val writer = new PrintWriter(new File(fileName))

    try {
      println(s"Dumping the visual recipe ...")
      writer.write(compiledRecipe.getRecipeVisualization)
      println(s"Dumped here: $fileName")
    } finally {
      writer.close()
    }
  }

  def logRecipeStats(recipe: Recipe): Unit = println(s"Generated recipe ::: " +
    s"name: ${recipe.name} " +
    s"nrOfSensoryEvents: ${recipe.sensoryEvents.size} " +
    s"nrOfInteractions: ${recipe.interactions.size} " +
    s"")

  def logCompiledRecipeStats(compiledRecipe: CompiledRecipe): Unit = println(s"Compiled recipe ::: " +
    s"name: ${compiledRecipe.name} " +
    s"nrOfAllIngredients: ${compiledRecipe.ingredients.size} " +
    s"nrOfSensoryEvents: ${compiledRecipe.sensoryEvents.size} " +
    s"nrOfInteractionEvents: ${compiledRecipe.interactionEvents.size} " +
    s"nrOfInteractions: ${compiledRecipe.interactionTransitions.size} " +
    s"")

}

