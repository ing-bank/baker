package com.ing.baker.runtime.recipe

import com.ing.baker.runtime.core.ProcessState
import com.ing.baker.runtime.recipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.runtime.recipe.transitions.InteractionTransition
import com.ing.baker.runtime.recipe.transitions.ProvidesType.{ProvidesEvent, ProvidesIngredient}
import com.ing.baker.runtime.visualization.RecipeVisualizer
import io.kagera.api.colored._

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: ExecutablePetriNet[ProcessState],
                          initialMarking: Marking,
                          sensoryEvents: Set[Class[_]],
                          ingredientExtractor: IngredientExtractor,
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

  def transitionForEventClass(eventClass: Class[_]) =
  //TODO move te setting of this to the compiler and not as part of the compiled recipe itself
    petriNet.transitions.findByLabel(eventClass.getSimpleName).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $eventClass")
    }

  val interactionEvents: Set[Class[_]] =
    interactionTransitions flatMap  {
      case InteractionTransition(_, providesType: ProvidesEvent, _, _, _, _, _, _, _, _, _, _) => providesType.outputEventClasses
      case _ => Seq.empty
    }

  val allEvents: Set[Class[_]] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByInteractions: Set[(String, Class[_])] =
    interactionTransitions map {
      case InteractionTransition(_, providesType: ProvidesIngredient, _, _, _, _, _, _, _, _, _, _) => providesType.outputIngredient
      case _ => null
    } filterNot(_ == null)


  val allIngredientsProvidedByEvents: Set[(String, Class[_])] = allEvents.flatMap {
    eventClass => ingredientExtractor.extractIngredientTypes(eventClass)
  }

  val ingredients: Map[String, Class[_]] =
  //TODO move te setting of this to the compiler and not as part of the compiled recipe itself
    (allIngredientsProvidedByInteractions ++ allIngredientsProvidedByEvents).toMap
}
