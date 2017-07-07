package com.ing.baker.pbt

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Recipe}
import org.scalacheck._
import org.scalacheck.Prop.forAll

class RecipeProperties extends Properties("Properties of a Recipe") {

  property("recipe compiles without validation errors") = forAll(recipeGen) { recipe =>
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
    println(s"Nr of ingredients for recipe ${compiledRecipe.name}: ${compiledRecipe.ingredients.size}")
    compiledRecipe.validationErrors.isEmpty
  }

  val ingredientGen: Gen[Ingredient[_]] = for {
    name <- Gen.uuid.map(_.toString)
  } yield Ingredient[String](s"ingredient-$name")

  val eventGen: Gen[Event] = for {
    name <- Gen.uuid.map(_.toString)
    providedIngredient <- ingredientGen
  } yield Event(s"event-$name", Seq(providedIngredient))

  val recipeGen: Gen[Recipe] = for {
    name <- Gen.uuid.map(_.toString)
    sensoryEvents <- Gen.listOfN(5, eventGen)
  } yield Recipe(s"recipe-$name").withSensoryEvents(sensoryEvents: _*)

}
