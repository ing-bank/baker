package com.ing.baker.pbt

import java.io.{File, PrintWriter}

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionOutput, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, Recipe}
import org.scalacheck.Prop.forAll
import org.scalacheck._
import org.scalatest.FunSuite
import org.scalatest.prop.Checkers

import scala.annotation.tailrec
import scala.util.Random

class RecipePropertiesSpec extends FunSuite with Checkers {

  import RecipePropertiesSpec._

  test("compiles with no errors") {
    val prop = forAll(recipeGen) { recipe =>

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

      if (compiledRecipe.validationErrors.nonEmpty) {
        logRecipeStats(recipe)
        logCompiledRecipeStats(compiledRecipe)
        dumpVisualRecipe(recipeVisualizationOutputPath, compiledRecipe)
      }

      // assertion of the result
      compiledRecipe.validationErrors.isEmpty
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(1000))
  }
}

object RecipePropertiesSpec {

  val maxNrOfIngredientsPerEvent = 3
  val maxNrOfOutputEventsPerInteraction = 3
  val maxNrOfIngredientsToConsume = 10
  val recipeVisualizationOutputPath: String = System.getProperty("java.io.tmpdir")

  val nameGen: Gen[String] = Gen.listOfN(8, Gen.alphaNumChar).map(_.mkString)

  val ingredientGen: Gen[Ingredient[_]] = for {
    name <- nameGen
  } yield Ingredient[String](name)

  val eventGen: Gen[Event] = for {
    name <- nameGen
    nrOfIngredients <- Gen.frequency(
      1 -> Gen.const(0),
      10 -> Gen.choose(1, maxNrOfIngredientsPerEvent)
    )
    providedIngredients <- Gen.listOfN(nrOfIngredients, ingredientGen)
  } yield Event(name, providedIngredients)

  val recipeGen: Gen[Recipe] = for {
    name <- nameGen
    sensoryEvents <- Gen.listOf(eventGen)
    interactions <- interactionsGen(getIngredientsFrom(sensoryEvents))
  } yield Recipe(name)
    //turn the lists into var args
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions: _*)

  def interactionsGen(ingredients: Seq[common.Ingredient]): Gen[List[InteractionDescriptor]] = Gen.const(getInteractions(ingredients))

  def getInteractions(withIngredients: Seq[common.Ingredient]): List[InteractionDescriptor] = {
    @tailrec def interaction(ingredients: List[common.Ingredient], acc: List[InteractionDescriptor]): List[InteractionDescriptor] = ingredients match {
      case Nil => acc
      case ingredientsLeft =>
        //take a subset of ingredients
        // TODO implement supporting also 0 input ingredients for interactions with required events
        val nrOfIngredientsToConsume = ingredientsLeft.length min sample(Gen.choose(1, maxNrOfIngredientsToConsume))
        val pickedIngredients = Random.shuffle(ingredientsLeft).take(nrOfIngredientsToConsume)
        val remainingIngredients = ingredients.diff(pickedIngredients)

        val (interactionDescriptor, outputIngredients) = getDescriptor(pickedIngredients)

        if (remainingIngredients.isEmpty)
        //those are the last ingredients because the diff is an empty list, so nothing left to weave
          interactionDescriptor :: acc
        else
          interaction(remainingIngredients ++ outputIngredients, interactionDescriptor :: acc)
    }

    interaction(withIngredients.toList, List.empty)
  }

  val interactionOutputGen: Gen[InteractionOutput] = for {
    nrOfEvents <- Gen.choose(0, maxNrOfOutputEventsPerInteraction)
    events <- Gen.listOfN(nrOfEvents, eventGen)
    ingredient <- ingredientGen
    output <- Gen.frequency(
//      1 -> Gen.const(ProvidesNothing),
      5 -> Gen.const(ProvidesIngredient(ingredient)),
      10 -> Gen.const(FiresOneOfEvents(events)))
  } yield output

  @tailrec def sample[T](gen: Gen[T]): T = gen.sample match {
    case Some(value) => value
    case None => sample(gen)
  }

  def getDescriptor(ingredients: Seq[common.Ingredient]): (InteractionDescriptor, List[common.Ingredient]) = {
    //each interaction fires a single event
    val output = sample(interactionOutputGen)
    val interaction = Interaction(sample(nameGen), ingredients, output)

    //return the interaction description and a list of all ingredients that the interaction provides
    val outputIngredients: List[common.Ingredient] = output match {
      case ProvidesNothing => Nil
      case FiresOneOfEvents(events) => getIngredientsFrom(events.toList)
      case ProvidesIngredient(ingredient) => List(ingredient)
    }

    (InteractionDescriptor(interaction), outputIngredients)
  }

  def getIngredientsFrom(events: List[common.Event]): List[common.Ingredient] = events.flatMap(_.providedIngredients)

  def logRecipeStats(recipe: Recipe): Unit = println(s"Generated recipe ::: " +
    s"name: ${recipe.name} " +
    s"nrOfSensoryEvents: ${recipe.sensoryEvents.size} " +
    s"nrOfInteractions: ${recipe.interactions.size} " +
    s"")

  def logCompiledRecipeStats(compiledRecipe: CompiledRecipe): Unit = {
    println(s"Compiled recipe ::: " +
      s"name: ${compiledRecipe.name} " +
      s"nrOfAllIngredients: ${compiledRecipe.ingredients.size} " +
      s"nrOfSensoryEvents: ${compiledRecipe.sensoryEvents.size} " +
      s"nrOfInteractionEvents: ${compiledRecipe.interactionEvents.size} " +
      s"nrOfInteractions: ${compiledRecipe.interactionTransitions.size} " +
      s"")
    if (compiledRecipe.validationErrors.nonEmpty) println(s"***VALIDATION ERRORS: ${compiledRecipe.validationErrors.mkString("\n")}")
  }

  def dumpVisualRecipe(dumpDir: String, compiledRecipe: CompiledRecipe): Unit = {
    val fileName =
      if (dumpDir endsWith "/") s"$dumpDir${compiledRecipe.name}.dot"
      else s"$dumpDir/${compiledRecipe.name}.dot"

    val outFile = new File(fileName)
    val writer = new PrintWriter(outFile)

    try {
      println(s"Generating the visual recipe ...")
      val dotRepresentation = compiledRecipe.getRecipeVisualization
      writer.write(dotRepresentation)
      println(s"Recipe visualization in bytes: ${dotRepresentation.length}. Dump location: $fileName \n")
    } finally {
      writer.close()
    }
  }

}
