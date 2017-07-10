package com.ing.baker.pbt

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.ProvidesNothing
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, Recipe}
import org.scalacheck.Prop.forAll
import org.scalacheck._

class RecipeProperties extends Properties("Properties of a Recipe") {

  property("recipe compiles without validation errors") = forAll(recipeGen) { recipe =>
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
    println(s"PBT stats: recipeName: ${compiledRecipe.name} " +
      s"nrOfIngredients: ${compiledRecipe.ingredients.size} " +
      s"nrOfEvents: ${compiledRecipe.allEvents.size} " +
      s"nrOfInteractionTransitions: ${compiledRecipe.interactionTransitions.size}")

    if (compiledRecipe.validationErrors.nonEmpty) {
      println(s"Validation errors: ${compiledRecipe.validationErrors}")
      println(s"Visual recipe: ${compiledRecipe.getRecipeVisualization}")
    }

    compiledRecipe.validationErrors.isEmpty
  }

  val sampleSize = 1000
  val ingredientPool: Seq[Ingredient[_]] = for (idx <- 0 until sampleSize) yield Ingredient[String](s"ingredient-$idx")

  val eventPool: Seq[Event] = {
    def pickEvent(idx: Int, ingredients: Seq[Ingredient[_]]): Seq[Event] = {
      if (ingredients.isEmpty) {
        val event = Event(s"event-$idx", ingredients)
        println(s"Generated event ${event.name} with ${ingredients.size} ingredients")
        Seq(event)
      } else {
        val taken = Gen.someOf(ingredients).sample.getOrElse(Seq())
        val remaining = ingredients.diff(taken)

        val event = Event(s"event-$idx", taken)
        println(s"Generated event ${event.name} with ${taken.size} ingredients")
        Seq(event) ++ pickEvent(idx+1, remaining)
      }
    }
    println("***Generating sequence of events...")
    pickEvent(0, ingredientPool)
  }

  def interactions(events: Seq[Event]): Seq[InteractionDescriptor] = {
    def pickInteraction(idx: Int, events: Seq[Event]): Seq[InteractionDescriptor] = {
      if (events.isEmpty) {
        val interaction = InteractionDescriptor(Interaction(s"interaction-$idx", Seq.empty, ProvidesNothing()))
        println(s"Generated interaction ${interaction.name} with 0 input ingredients")
        Seq(interaction)
      } else {
        val taken = Gen.someOf(events).sample.getOrElse(Seq())
        val remaining = events.diff(taken)
        val inputIngredients = taken.flatMap(_.providedIngredients)

        val interaction = InteractionDescriptor(Interaction(s"interaction-$idx", inputIngredients, ProvidesNothing()))
        println(s"Generated interaction ${interaction.name} with ${inputIngredients.size} input ingredients")
        Seq(interaction) ++ pickInteraction(idx+1, remaining)
      }
    }
    println("***Generating sequence of interactions...")
    pickInteraction(0, events)
  }

//    for {
//      name <- Gen.uuid.map(_.toString)
//      inputIngredients <- Gen.listOf(ingredientGen)
//      outputIngredient <- ingredientGen
//    } yield InteractionDescriptor(Interaction(s"interaction-$name", inputIngredients, ProvidesIngredient(outputIngredient)))

  val recipeGen: Gen[Recipe] = for {
    recipeName <- Gen.uuid.map(_.toString)
    sensoryEvents <- Gen.someOf(eventPool)
    _ = println(s"nrOfSensoryEvents=${sensoryEvents.size}")
//    _ = sensoryEvents.foreach(event => println(s"ingredients in each event: ${event.providedIngredients.size}"))
  } yield Recipe(s"recipe-$recipeName")
      .withSensoryEvents(sensoryEvents: _*)
      .withInteractions(interactions(sensoryEvents): _*)

}
