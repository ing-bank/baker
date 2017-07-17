package com.ing.baker.pbt

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.pbt.RecipePropertiesSpec._
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.FiresOneOfEvents
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, Recipe}
import org.scalacheck._
import org.scalatest.FunSuite
import org.scalatest.prop.Checkers._

import scala.annotation.tailrec
import scala.util.Random

class RecipeDesignPropertiesSpec extends FunSuite {
  import Prop.forAll
  import RecipeDesignPropertiesSpec._

  test("compiles with no errors") {
    val property = forAll(recipesGen) { recipe =>
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

    check(property, Test.Parameters.defaultVerbose.withMinSuccessfulTests(100))
  }
}

object RecipeDesignPropertiesSpec {

  val maxNrOfIngredientsPerEvent = 3
  val recipeVisualizationOutputPath: String = System.getProperty("java.io.tmpdir")

  val ingredientGen: Gen[Ingredient[_]] = for {
    name <- Gen.uuid
  } yield Ingredient[String](name.toString)

  val eventGen: Gen[Event] = for {
    name <- Gen.uuid
    providedIngredients <- Gen.listOfN(maxNrOfIngredientsPerEvent, ingredientGen)
  } yield Event(name.toString, providedIngredients)

  val recipesGen: Gen[Recipe] = for {
    name <- Gen.uuid
    sensoryEvents <- Gen.listOf(eventGen)
    interactions <- interactionsGen(getIngredientsFrom(sensoryEvents))
  } yield Recipe(name.toString)
    //turn the lists into var args
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions: _*)

  def interactionsGen(ingredients: Seq[common.Ingredient]): Gen[List[InteractionDescriptor]] = Gen.const(getInteractions(ingredients))

  def getInteractions(withIngredients: Seq[common.Ingredient]): List[InteractionDescriptor] = {
    @tailrec def interaction(ingredients: List[common.Ingredient], acc: List[InteractionDescriptor]): List[InteractionDescriptor] = ingredients match {
      case Nil => acc
      case ingredientsLeft =>
        //take at least one ingredient
        val requiredIngredients = Random.shuffle(ingredientsLeft).take(Gen.choose(1, ingredientsLeft.length).sample.getOrElse(1))

        val output = getDescriptor(requiredIngredients)

        if(ingredients.diff(requiredIngredients).isEmpty)
        //those are the last ingredients because the diff is an empty list, so nothing left to weave
          output._1 :: acc
        else
          interaction(ingredients.diff(requiredIngredients) ++ output._2, output._1 :: acc)
    }

    interaction(withIngredients.toList, List.empty)
  }

  def getDescriptor(ingredients: Seq[common.Ingredient]): (InteractionDescriptor, List[common.Ingredient]) = {
    //each interaction fires a single event
    val output = FiresOneOfEvents(Seq(eventGen.sample.get))
    val interaction = Interaction(Gen.uuid.sample.get.toString, ingredients, output)
    //return the interaction description and a list of all ingredients that the interaction provides (via the single event)
    (InteractionDescriptor(interaction), output.events.flatMap(e => e.providedIngredients).toList)
  }

  def getIngredientsFrom(events: List[Event]): Seq[common.Ingredient] = events.flatMap(_.providedIngredients)
}
