package com.ing.baker.runtime.model

import java.util.UUID

import cats.effect.ConcurrentEffect
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceF}
import org.mockito.Matchers.{eq => mockitoEq, _}
import org.mockito.Mockito._

import scala.concurrent.duration._
import scala.reflect.ClassTag

trait BakerModelSpecEnquireTests[F[_]] { self: BakerModelSpec[F] =>

  def runEnquireTests()(implicit effect: ConcurrentEffect[F], classTag: ClassTag[F[Any]]): Unit = {
    test("return recipe if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipe <- baker.getRecipe(recipeId)
      } yield recipe.compiledRecipe.name shouldBe "returnRecipe"
    }

    test("return all recipes if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnAllRecipes", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnAllRecipes2")))
        recipes <- baker.getAllRecipes
        _ = recipes.size shouldBe 2
        _ = recipes(recipeId).compiledRecipe.name shouldBe "returnAllRecipes"
        _ = recipes(recipeId2).compiledRecipe.name shouldBe "returnAllRecipes2"
      } yield succeed
    }

    test("return no errors of a recipe with no errors if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnHealthRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeInformation <- baker.getRecipe(recipeId)
        _ = assert(recipeInformation.compiledRecipe.recipeId == recipeId && recipeInformation.errors.isEmpty)
      } yield succeed
    }

    test("return no errors of all recipes if none contain errors if asked") { context =>
      for {
        bakerWithRecipe <- context.setupBakerWithRecipe("returnHealthAllRecipe", appendUUIDToTheRecipeName = false)
        (baker, recipeId) = bakerWithRecipe
        recipeId2 <- baker.addRecipe(RecipeCompiler.compileRecipe(getRecipe("returnHealthAllRecipe2")))
        recipeInformations <- baker.getAllRecipes
        _ = recipeInformations.size shouldBe 2
        _ = recipeInformations.get(recipeId)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId && r.errors.isEmpty))
        _ = recipeInformations.get(recipeId2)
          .foreach(r => assert(r.compiledRecipe.recipeId == recipeId2 && r.errors.isEmpty))
      } yield succeed
    }

    test("be able to visualize events that have been fired") { context =>
      //This test only checks if the graphviz is different, not that the outcome is correct
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe("CheckEventRecipe")
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        noEventsGraph <- baker.getVisualState(recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        firstEventGraph <- baker.getVisualState(recipeInstanceId)
        //System.out.println(firstEventGraph)
        _ = noEventsGraph should not be firstEventGraph
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        secondEventGraph <- baker.getVisualState(recipeInstanceId)
        //System.out.println(secondEventGraph)
        _ = firstEventGraph should not be secondEventGraph
      } yield succeed
    }
/*
    test("testy test") { context =>
      val recipe = Recipe("TestyTestRecipe")
        .withInteractions(
          interactionFour
            .withRequiredEvents(secondEvent),
        )
        .withSensoryEvents(
          eventFromInteractionTwo,
          secondEvent)
      for {
        bakerAndRecipeId <- context.setupBakerWithRecipe(recipe, Seq(InteractionInstanceF.unsafeFrom[F](testInteractionFourMock)))
        (baker, recipeId) = bakerAndRecipeId
        recipeInstanceId = UUID.randomUUID().toString
        _ = when(testInteractionFourMock.apply()).thenReturn(InteractionFourSuccessful("success-ingredient"))
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventFromInteractionTwo("my-ingredient-value")))
        vis <- baker.getVisualState(recipeInstanceId)
        compiled = RecipeCompiler.compileRecipe(recipe)
        visPetri = compiled.getPetriNetVisualization
        _ = println()
        _ = println(vis)
        _ = println()
        _ <- timer.sleep(1.seconds).to[F]
      } yield succeed
    }
*/
  }
}
