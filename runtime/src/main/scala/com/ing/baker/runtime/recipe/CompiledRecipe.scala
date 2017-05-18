package com.ing.baker.runtime.recipe

import com.ing.baker.runtime.core.ProcessState
import com.ing.baker.runtime.recipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.runtime.recipe.transitions.InteractionTransition
import com.ing.baker.runtime.recipe.transitions.ProvidesType.{ProvidesEvent, ProvidesIngredient}
import com.ing.baker.runtime.visualization.RecipeVisualizer.PetriNetVisualization
import io.kagera.api.colored._
import io.kagera.dot.{GraphDot, PetriNetDot}

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: ExecutablePetriNet[ProcessState],
                          initialMarking: Marking,
                          sensoryEvents: Set[Class[_]],
                          ingredientExtractor: IngredientExtractor,
                          validationErrors: Seq[String] = Seq.empty) {


  def getRecipeVisualization: String = petriNet.innerGraph.toDot(x => true)

  /**
    * Returns a DOT ((http://www.graphviz.org/)) representation of the recipe filtering out those nodes / edges that match the filter.
    */
  def getFilteredRecipeVisualization(filterFunc: String => Boolean): String =
    petriNet.innerGraph.toDot(filterFunc)

  def getPetriNetVisualization: String =
    GraphDot
      .generateDot(petriNet.innerGraph, PetriNetDot.petriNetTheme[Place[_], Transition[_, _, _]])

  val interactionTransitions: Set[InteractionTransition[_]] = petriNet.transitions.collect {
    case t: InteractionTransition[_] => t
  }

  def transitionForEventClass(eventClass: Class[_]) =
  //TODO move te setting of this to the compiler and not as part of the compiled recipe itself
    petriNet.transitions.findByLabel(eventClass.getSimpleName).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $eventClass")
    }

  val interactionEvents: Set[Class[_]] =
    interactionTransitions.flatMap(
      _.providesType match {
        case ProvidesEvent(_, _, outputEventClasses) => outputEventClasses
        case _ => Nil
      }
    )

  val allEvents: Set[Class[_]] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByInteractions: Set[(String, Class[_])] =
    interactionTransitions.map {
      _.providesType match {
        case ProvidesIngredient(outputIngredient: (String, Class[_]), _) => outputIngredient
        case _ => None.asInstanceOf[(String, Class[_])]
      }
    }

  val allIngredientsProvidedByEvents = allEvents.flatMap {
    eventClass => ingredientExtractor.extractIngredientTypes(eventClass)
  }

  val ingredients: Map[String, Class[_]] =
  //TODO move te setting of this to the compiler and not as part of the compiled recipe itself
    (allIngredientsProvidedByInteractions ++ allIngredientsProvidedByInteractions).toMap
}
