package com.ing.baker.il

import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, RecipePetriNet}
import com.ing.baker.petrinet.api.Marking

import scala.collection.JavaConverters._
import scala.concurrent.duration.FiniteDuration

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: RecipePetriNet,
                          initialMarking: Marking[Place],
                          validationErrors: Seq[String] = Seq.empty,
                          eventReceivePeriod: Option[FiniteDuration],
                          retentionPeriod: Option[FiniteDuration]) {

  def sensoryEvents: Set[EventDescriptor] = petriNet.transitions.collect {
    case EventTransition(eventDescriptor, true, _) => eventDescriptor
  }.toSet

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

  val interactionEvents: Set[EventDescriptor] = interactionTransitions flatMap(it => it.eventsToFire)

  val allEvents: Set[EventDescriptor] = sensoryEvents ++ interactionEvents

  def getAllEvents: java.util.Set[EventDescriptor] = allEvents.asJava

  val allIngredients: Set[IngredientDescriptor] = allEvents.flatMap {
    events => events.ingredients
  }

  def getAllIngredients: java.util.Set[IngredientDescriptor] = allIngredients.asJava
}
