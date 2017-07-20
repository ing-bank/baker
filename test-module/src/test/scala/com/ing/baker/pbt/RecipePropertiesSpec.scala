package com.ing.baker.pbt

import java.io.{File, PrintWriter}

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionOutput, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, InteractionDescriptorFactory, Recipe}
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
  val maxNrOfPreconditionEvents = 3
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

  val interactionOutputGen: Gen[InteractionOutput] = for {
    nrOfEvents <- Gen.choose(0, maxNrOfOutputEventsPerInteraction)
    events <- Gen.listOfN(nrOfEvents, eventGen)
    ingredient <- ingredientGen
    output <- Gen.frequency(
      //      1 -> Gen.const(ProvidesNothing),
      5 -> Gen.const(ProvidesIngredient(ingredient)),
      10 -> Gen.const(FiresOneOfEvents(events)))
  } yield output

  val recipeGen: Gen[Recipe] = for {
    name <- nameGen
    sensoryEvents <- Gen.listOf(eventGen)
    interactions <- interactionsGen(sensoryEvents)
  } yield Recipe(name)
    //turn the lists into var args
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions.toList: _*)

  def interactionsGen(events: Iterable[common.Event]): Gen[Set[InteractionDescriptor]] = Gen.const(getInteractions(events))

  def getInteractions(sensoryEvents: Iterable[common.Event]): Set[InteractionDescriptor] = {
    @tailrec def interaction(ingredients: Set[common.Ingredient], events: Set[common.Event], acc: Set[InteractionDescriptor]): Set[InteractionDescriptor] = ingredients match {
      case _ingredients if _ingredients.isEmpty => acc
      case ingredientsLeft =>
        //take a subset of ingredients
        // TODO implement supporting also 0 input ingredients for interactions with required events
        val nrOfIngredientsToConsume = ingredientsLeft.size min sample(Gen.choose(1, maxNrOfIngredientsToConsume))
        val pickedIngredients = Random.shuffle(ingredientsLeft).take(nrOfIngredientsToConsume)
        val remainingIngredients = ingredients.diff(pickedIngredients)

        val (interactionDescriptor, outputIngredients, outputEvents) = getInteractionDescriptor(pickedIngredients, events)

        if (remainingIngredients.isEmpty)
        //those are the last ingredients because the diff is an empty list, so nothing left to weave
          acc + interactionDescriptor
        else
          interaction(
            remainingIngredients ++ outputIngredients ++ getIngredientsFrom(outputEvents),
            events ++ outputEvents,
            acc + interactionDescriptor)
    }

    val ingredients = getIngredientsFrom(sensoryEvents)
    interaction(ingredients, sensoryEvents.toSet, Set.empty)
  }

  def getInteractionDescriptor(ingredients: Set[common.Ingredient], events: Set[common.Event]): (InteractionDescriptor, Set[common.Ingredient], Set[common.Event]) = {
    //each interaction fires a single event
    val output = sample(interactionOutputGen)
    val interaction = Interaction(sample(nameGen), ingredients.toSeq, output)

    //return the interaction description and a list of all ingredients that the interaction provides
    val (outputIngredients: Set[common.Ingredient], outputEvents: Set[common.Event]) = output match {
      case ProvidesNothing => (Set.empty, Set.empty)
      case FiresOneOfEvents(_events) => (Set.empty, _events.toSet)
      case ProvidesIngredient(ingredient) => (Set(ingredient), Set.empty)
    }

    val nrOfAndPreconditionEvents = sample(Gen.chooseNum(0, maxNrOfPreconditionEvents))
    val nrOfOrPreconditionEvents = sample(Gen.chooseNum(0, maxNrOfPreconditionEvents))

    val andPreconditionEvents: Set[common.Event] = Random.shuffle(events).take(nrOfAndPreconditionEvents)
    val orPreconditionEvents: Set[common.Event] = {
      val pickedEvents = Random.shuffle(events -- andPreconditionEvents).take(nrOfOrPreconditionEvents)
      if (pickedEvents.size < 2) Set.empty
      else pickedEvents
    }

    val interactionDescriptor = InteractionDescriptorFactory(interaction)
      .withRequiredEvents(andPreconditionEvents.toList: _*)
      .withRequiredOneOfEvents(orPreconditionEvents.toList: _*)

    (interactionDescriptor, outputIngredients, outputEvents)
  }

  def getIngredientsFrom(events: Iterable[common.Event]): Set[common.Ingredient] = events.flatMap(_.providedIngredients).toSet

  @tailrec def sample[T](gen: Gen[T]): T = gen.sample match {
    case Some(value) => value
    case None => sample(gen)
  }

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
