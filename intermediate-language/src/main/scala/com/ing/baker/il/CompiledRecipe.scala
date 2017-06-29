package com.ing.baker.il

import com.ing.baker.il.petrinet.{FiresOneOfEvents, InteractionTransition, Place, ProvidesIngredient, RecipePetriNet}
import io.kagera.api._

import scala.collection.JavaConverters._

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: RecipePetriNet,
                          initialMarking: Marking[Place],
                          sensoryEvents: Set[EventType],
                          validationErrors: Seq[String] = Seq.empty) {

  def getValidationErrors: java.util.List[String] = validationErrors.toList.asJava

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


  def getFilteredRecipeVisualization(filter: String): String =
    getFilteredRecipeVisualization(x => !x.contains(filter))

  /**
    * Returns a DOT (http://www.graphviz.org/) representation of the recipe.
    * All events/interaction/ingredients that contain one of the given filter strings are filtered out
    *
    * @param filters
    * @return
    */
  def getFilteredRecipeVisualization(filters: Array[String]): String =
    getFilteredRecipeVisualization((current) => filters.forall(filter => !current.contains(filter)))

  /**
    * Visualises the underlying petri net in DOT format
    * @return
    */
  def getPetriNetVisualization: String =
    RecipeVisualizer.visualisePetrinetOfCompiledRecipe(petriNet)

  val interactionTransitions: Set[InteractionTransition[_]] = petriNet.transitions.collect {
    case t: InteractionTransition[_] => t
  }

  val interactionEvents: Set[EventType] =
    interactionTransitions flatMap  {
      case InteractionTransition(providesType: FiresOneOfEvents, _, _, _, _, _, _, _, _) => providesType.events
      case _ => Seq.empty
    }

  val allEvents: Set[EventType] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByInteractions: Set[IngredientType] =
    interactionTransitions map {
      case InteractionTransition(providesType: ProvidesIngredient, _, _, _, _, _, _, _, _) => providesType.ingredient
      case _ => null
    } filterNot(_ == null)


  val allIngredientsProvidedByEvents: Set[IngredientType] = allEvents.flatMap {
    events => events.providedIngredients
  }

  val ingredients: Map[String, IngredientType] = (allIngredientsProvidedByInteractions ++ allIngredientsProvidedByEvents).map(i => i.name -> i).toMap
}
