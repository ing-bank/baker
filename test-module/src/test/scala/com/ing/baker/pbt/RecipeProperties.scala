package com.ing.baker.pbt

import com.ing.baker.compiler.RecipeCompiler
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

//    if (compiledRecipe.interactionTransitions.size > 2) {
//      println(s"Visual recipe: ${compiledRecipe.getRecipeVisualization}")
//    }

    compiledRecipe.validationErrors.isEmpty
  }

}

object RecipeProperties {
  val sampleSize = 10
  val ingredientPoolForSensoryEvents: Seq[Ingredient[_]] = for (idx <- 0 until sampleSize) yield Ingredient[String](s"ingredient-$idx")

  val sensoryEventPool: Seq[Event] = {
    def pickEventLoop(idx: Int, ingredients: Seq[Ingredient[_]]): Seq[Event] = {
      if (ingredients.isEmpty) {
        val event = Event(s"event-$idx", ingredients)
//        println(s"Generated event ${event.name} with ${ingredients.size} ingredients")
        Seq(event)
      } else {
        val taken = Gen.someOf(ingredients).sample.getOrElse(Seq.empty)
        val remaining = ingredients.diff(taken)

        val event = Event(s"sensory-event-$idx", taken)
//        println(s"Generated event ${event.name} with ${taken.size} ingredients")
        Seq(event) ++ pickEventLoop(idx+1, remaining)
      }
    }
//    println("***Generating sequence of events...")
    pickEventLoop(0, ingredientPoolForSensoryEvents)
  }

  val ingredientGen: Gen[Ingredient[_]] = for {
    ingredientName <- Gen.uuid.map(_.toString)
  } yield Ingredient[String](s"ingredient-$ingredientName")

  val interactionEventGen: Gen[Event] = for {
    eventName <- Gen.uuid.map(_.toString)
    ingredients <- Gen.listOfN(Random.nextInt(10), ingredientGen)
  } yield Event(s"event-$eventName", ingredients)

  println(s"============ EVENT POOL SIZE: ${sensoryEventPool.size}")

  def interactions(events: Seq[Event], recipeName: String): Seq[InteractionDescriptor] = {

    def pickInteractionLoop(idx: Int, events: Seq[Event], interactionEvents: Seq[Event]): Seq[InteractionDescriptor] = {
//      if (events.isEmpty || idx > 5) {
      if (events.isEmpty) {
        Seq.empty
      } else {
        val takenEvents = Gen.someOf(events ++ interactionEvents).sample.getOrElse(events.take(1))
        val inputIngredients = takenEvents.flatMap(_.providedIngredients)
        val remainingEvents = events.diff(takenEvents)

        val takenInteractionEvents = Gen.listOfN(Random.nextInt(10), interactionEventGen).sample.getOrElse(Seq.empty)

        // Do not generate an interaction with 0 ingredients, this is not a valid recipe. Skip this round.
        if (inputIngredients.isEmpty) {
//          println("Sample input ingredient list is empty, skipping this round of Interaction generation.")
          Seq.empty ++ pickInteractionLoop(idx, remainingEvents, interactionEvents)
        } else {
          val interactionOutput = FiresOneOfEvents(takenInteractionEvents)
          val interaction = InteractionDescriptor(Interaction(s"interaction-$idx", inputIngredients, interactionOutput))
//          println(s"Generated interaction ${interaction.name} with ${inputIngredients.size} input ingredients")
          Seq(interaction) ++ pickInteractionLoop(idx+1, remainingEvents, interactionEvents ++ takenInteractionEvents)
        }

      }
    }

//    println(s"***Generating sequence of interactions for recipe $recipeName... with initial events: $events")
    pickInteractionLoop(0, events, Seq.empty)
  }

  val recipeGen: Gen[Recipe] = for {
    recipeName <- Gen.uuid.map(_.toString)
    sensoryEvents <- Gen.someOf(sensoryEventPool)
//    interactionEvents <- Gen.someOf(eventPool.diff(sensoryEvents))
//    _ = println(s"nrOfSensoryEvents=${sensoryEvents.size}")
  //    _ = sensoryEvents.foreach(event => println(s"ingredients in each event: ${event.providedIngredients.size}"))
  } yield Recipe(s"recipe-$recipeName")
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions(sensoryEvents, recipeName): _*)


}

