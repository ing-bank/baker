package com.ing.baker.pbt

import java.io.{File, PrintWriter}
import java.util.UUID

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.common.FiresOneOfEvents
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, Recipe}
import org.scalacheck.Prop.forAll
import org.scalacheck._

import scala.util.Random

class RecipeProperties extends Properties("Properties of a Recipe") {

  import RecipeProperties._

  property("recipe compiles without validation errors") = forAll(recipeGen) { recipe =>

    //    println(s"===============================================================Recipe under test: ${recipe.name}")
    //    println(s"Interactions: ${recipe.interactions.map(_.name).mkString(" ")}")
    //    println(s"Interaction Outputs: ${recipe.interactions.map(_.interaction.output).mkString(" ")}")
    //    println(s"Sensory events: ${recipe.sensoryEvents.map(_.name).mkString(" ")}")
    //    println("===============================================================")

    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    println(s"PBT stats: recipeName: ${compiledRecipe.name} " +
      s"nrOfAllIngredients: ${compiledRecipe.ingredients.size} " +
      s"nrOfSensoryEvents: ${compiledRecipe.sensoryEvents.size} " +
      s"nrOfInteractionEvents: ${compiledRecipe.interactionEvents.size} " +
      s"nrOfInteractions: ${compiledRecipe.interactionTransitions.size}")

    if (compiledRecipe.validationErrors.nonEmpty) {
      println(s"Validation errors: ${compiledRecipe.validationErrors}")
      println(s"Visual recipe: ${compiledRecipe.getRecipeVisualization}")
    }

    dumpVisualRecipe(recipeVisualizationOutputPath, compiledRecipe)

    compiledRecipe.validationErrors.isEmpty
  }

}

object RecipeProperties {
  ////////////////// start configuration

  // These parameters determine the size of the recipes
  val initialIngredientPoolUsedBySensoryEvents = 100
  val maxNrOfIngredientsPerEvent = 3
  val maxNrOfEventsComingInToAnInteraction = 3
  val maxNrOfInteractionEventsComingInToAnInteraction = 3
  val maxNrOfEventsGoingOutFromAnInteraction = 3

  // where to output the .dot files of the generated recipe visualizations
  val recipeVisualizationOutputPath: String = System.getProperty("java.io.tmpdir")

  ////////////////// end configuration

  val ingredientPoolForSensoryEvents: Seq[Ingredient[_]] = for (idx <- 0 until initialIngredientPoolUsedBySensoryEvents) yield Ingredient[String](s"ingredient-$idx")

  def rand(max: Int): Int = Random.nextInt(max)

  def uuid(): String = UUID.randomUUID().toString

  def randomIngredients(max: Int): Seq[Ingredient[_]] = for (_ <- 0 until rand(max)) yield Ingredient[String](s"ingredient-${uuid()}")

  def randomEvents(max: Int): Seq[Event] = for (_ <- 0 until rand(max)) yield Event(s"event-${uuid()}", randomIngredients(max))

  val sensoryEventPool: Seq[Event] = {
    def pickEventLoop(idx: Int, ingredients: Seq[Ingredient[_]]): Seq[Event] = {
      if (ingredients.isEmpty) {
        val event = Event(s"event-$idx", ingredients)
        Seq(event)
      } else {
        val taken = ingredients.take(rand(maxNrOfIngredientsPerEvent))
        val remaining = ingredients.diff(taken)

        val event = Event(s"sensory-event-$idx", taken)
        Seq(event) ++ pickEventLoop(idx + 1, remaining)
      }
    }

    pickEventLoop(0, ingredientPoolForSensoryEvents)
  }

  println(s"============ Started with $initialIngredientPoolUsedBySensoryEvents ingredients and generated ${sensoryEventPool.size} sensory events")

  def interactions(events: Seq[Event]): Seq[InteractionDescriptor] = {

    def pickInteractionLoop(idx: Int, events: Seq[Event], interactionEvents: Seq[Event]): Seq[InteractionDescriptor] = {
      if (events.isEmpty) {
        Seq.empty
      } else {
        val selectedEvents = events.take(rand(maxNrOfEventsComingInToAnInteraction))
        val selectedInteractionEvents = interactionEvents.take(rand(maxNrOfInteractionEventsComingInToAnInteraction))
        val inputIngredients = (selectedEvents ++ selectedInteractionEvents).flatMap(_.providedIngredients)
        val remainingEvents = events.diff(selectedEvents)

        // Do not generate an interaction with 0 ingredients, this is not a valid recipe. Skip this round.
        if (inputIngredients.isEmpty) {
          Seq.empty ++ pickInteractionLoop(idx, remainingEvents, interactionEvents)
        } else {
          val randomInteractionEvents = randomEvents(maxNrOfEventsGoingOutFromAnInteraction)
          val interactionOutput = FiresOneOfEvents(randomInteractionEvents)
          val interaction = InteractionDescriptor(Interaction(s"interaction-$idx", inputIngredients, interactionOutput))
          Seq(interaction) ++ pickInteractionLoop(idx + 1, remainingEvents, interactionEvents ++ randomInteractionEvents)
        }

      }
    }

    pickInteractionLoop(0, events, Seq.empty)
  }

  val recipeGen: Gen[Recipe] = for {
    sensoryEvents <- Gen.someOf(sensoryEventPool)
  } yield Recipe(s"recipe-${uuid()}")
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions(sensoryEvents): _*)

  def dumpVisualRecipe(dumpDir: String, compiledRecipe: CompiledRecipe): Unit = {
    val fileName =
      if (dumpDir endsWith "/") s"$dumpDir${compiledRecipe.name}.dot"
      else s"$dumpDir/${compiledRecipe.name}.dot"

    val writer = new PrintWriter(new File(fileName))

    try {
      println(s"Dumping the visual recipe here: $fileName")
      writer.write(compiledRecipe.getRecipeVisualization)
    } finally {
      writer.close()
    }

  }

}

