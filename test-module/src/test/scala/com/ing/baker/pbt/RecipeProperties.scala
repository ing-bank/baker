package com.ing.baker.pbt

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Recipe}
import org.scalacheck._
import org.scalacheck.Prop.forAll

class RecipeProperties extends Properties("Properties of a Recipe") {

  property("recipe compiles without validation errors") = forAll(recipeGen) { recipe =>
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
    println(s"PBT stats: recipeName:${compiledRecipe.name} nrOfIngredients: ${compiledRecipe.ingredients.size} nrOfEvents: ${compiledRecipe.allEvents.size}")
    compiledRecipe.validationErrors.isEmpty
  }

  val ingredientListGen: Gen[List[Ingredient[_]]] = for {
    names <- Gen.listOf(Gen.uuid.map(_.toString))
    name <- names
  } yield Ingredient[String](s"ingredient-$name")

  val eventGen: Gen[Event] = for {
    name <- Gen.uuid.map(_.toString)
    providedIngredients <- ingredientListGen
  } yield Event(s"event-$name", providedIngredients)

  val recipeGen: Gen[Recipe] = for {
    name <- Gen.uuid.map(_.toString)
    sensoryEvents <- Gen.listOf(eventGen)
  } yield Recipe(s"recipe-$name").withSensoryEvents(sensoryEvents: _*)

}
