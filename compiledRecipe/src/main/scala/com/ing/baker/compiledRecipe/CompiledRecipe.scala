package com.ing.baker.compiledRecipe

import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.ProvidesType.{ProvidesEvent, ProvidesIngredient}
import com.ing.baker.compiledRecipe.petrinet.{InteractionTransition, Place, RecipePetriNet}
import com.ing.baker.visualisation.RecipeVisualizer
import io.kagera.api._
/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: RecipePetriNet,
                          initialMarking: Marking[Place],
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

  val interactionEvents: Set[Class[_]] =
    interactionTransitions flatMap  {
      case InteractionTransition(_, providesType: ProvidesEvent, _, _, _, _, _, _, _, _) => providesType.outputEventClasses
      case _ => Seq.empty
    }

  val allEvents: Set[Class[_]] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByInteractions: Set[(String, Class[_])] =
    interactionTransitions map {
      case InteractionTransition(_, providesType: ProvidesIngredient, _, _, _, _, _, _, _, _) => providesType.outputIngredient
      case _ => null
    } filterNot(_ == null)


  val allIngredientsProvidedByEvents: Set[(String, Class[_])] = allEvents.flatMap {
    eventClass => ingredientExtractor.extractIngredientTypes(eventClass)
  }

  val ingredients: Map[String, Class[_]] = (allIngredientsProvidedByInteractions ++ allIngredientsProvidedByEvents).toMap
}
