package com.ing.baker

import java.util.UUID

import com.ing.baker.scala_api.SRecipe

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeVisualizationSpec extends TestRecipeHelper {

  implicit val timeout: FiniteDuration = 10 seconds

  before {
    resetMocks
  }

  override def afterAll {
    defaultActorSystem.terminate()
  }

  "The Baker engine" should {

    "be able to return all occurred events" in {

      val baker = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID()
      baker.bake(processId)

      //Handle first event
      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      val events = baker.events(processId)

      events.foreach(println)

      //Check if both the send in event and the events occured in baker are in the
      baker.events(processId) should contain only (
        InitialEvent("initialIngredient"),
        interactionTwoEvent
      )

      //Execute another event
      baker.handleEvent(processId, SecondEvent())

      //Check if both the send in event and the events occured in baker are in the
      baker.events(processId) should contain only (
        InitialEvent("initialIngredient"),
        interactionTwoEvent,
        SecondEvent()
      )
    }

    "be able to visualize the created interactions" in {
      val recipe: SRecipe = getComplexRecipe("VisiualizationRecipe")
      val compileRecipe = recipe.compileRecipe
//      System.out.println(compileRecipe.getPetriNetVisualization)
      System.out.println(compileRecipe.getRecipeVisualization)
      compileRecipe.getRecipeVisualization should include(
        "interactionOneIngredient -> InteractionThree")

      // Write visual recipe to a file so we can convert it to PNG easily
      // Online tool to use: http://mdaines.github.io/viz.js/
      // File("TestRecipe.dot").printlnAll(baker.recipe.getRecipeVisualization)

      // just to get an idea of how it looks like and to visualize it here: http://www.webgraphviz.com/
      // println(baker.recipe.getRecipeVisualization)
    }

    "be able to visualize the created interactions with a filter" in {
      val baker = setupBakerWithRecipe("VisualizationRecipe")
      baker.compiledRecipe.getFilteredRecipeVisualization(e => !e.contains("interactionFour")) shouldNot contain(
        "interactionFour")
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      val baker = setupBakerWithRecipe("CheckEventRecipe")

      val processId = UUID.randomUUID()
      baker.bake(processId)

      val noEventsGraph = baker.getVisualState(processId)
//      System.out.println(noEventsGraph)

      //Handle first event
      baker.handleEvent(processId, InitialEvent("initialIngredient"))

      val firstEventGraph = baker.getVisualState(processId)
//      System.out.println(firstEventGraph)

      noEventsGraph should not be firstEventGraph

      baker.handleEvent(processId, SecondEvent())
      val secondEventGraph = baker.getVisualState(processId)
//      System.out.println(secondEventGraph)

      firstEventGraph should not be secondEventGraph
    }
  }
}
