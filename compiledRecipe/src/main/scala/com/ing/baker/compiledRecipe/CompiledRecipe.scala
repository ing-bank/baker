package com.ing.baker.compiledRecipe

import com.ing.baker.compiledRecipe.petrinet.{FiresOneOfEvents, InteractionTransition, Place, ProvidesIngredient, RecipePetriNet}
import com.ing.baker.visualisation.RecipeVisualizer
import io.kagera.api._
/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: RecipePetriNet,
                          initialMarking: Marking[Place],
                          sensoryEvents: Set[RuntimeEvent],
                          validationErrors: Seq[String] = Seq.empty) {

  /**
    * Visualise the compiled recipe in DOT format
    * @return
    */
  def getRecipeVisualization: String =
    RecipeVisualizer.visualiseCompiledRecipe(this)

  /**
    * Visualise the compiled recipe in DOT format
    * @param filterFunc
    * @return
    */
  def getFilteredRecipeVisualization(filterFunc: String => Boolean): String =
    RecipeVisualizer.visualiseCompiledRecipe(this, filterFunc)

  /**
    * Visualises the underlying petri net in DOT format
    * @return
    */
  def getPetriNetVisualization: String =
    RecipeVisualizer.visualisePetrinetOfCompiledRecipe(petriNet)

  val interactionTransitions: Set[InteractionTransition[_]] = petriNet.transitions.collect {
    case t: InteractionTransition[_] => t
  }

  val interactionEvents: Set[RuntimeEvent] =
    interactionTransitions flatMap  {
      case InteractionTransition(providesType: FiresOneOfEvents, _, _, _, _, _, _, _) => providesType.events
      case _ => Seq.empty
    }

  val allEvents: Set[RuntimeEvent] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByInteractions: Set[RuntimeIngredient] =
    interactionTransitions map {
      case InteractionTransition(providesType: ProvidesIngredient, _, _, _, _, _, _, _) => providesType.ingredient
      case _ => null
    } filterNot(_ == null)


  val allIngredientsProvidedByEvents: Set[RuntimeIngredient] = allEvents.flatMap {
    events => events.providedIngredients
  }

  val ingredients: Map[String, RuntimeIngredient] = (allIngredientsProvidedByInteractions ++ allIngredientsProvidedByEvents).map(i => i.name -> i).toMap
}
