package com.ing.baker.compiler

import com.ing.baker.compiler.transitions.InteractionTransition
import com.ing.baker.RecipeVisualizer._
import com.ing.baker.core.ProcessState
import io.kagera.api.colored._
import io.kagera.dot.{GraphDot, PetriNetDot}

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: ExecutablePetriNet[ProcessState],
                          initialMarking: Marking,
                          sensoryEvents: Set[Class[_]],
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
    petriNet.transitions.findByLabel(eventClass.getSimpleName).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $eventClass")
    }

  val interactionEvents: Set[Class[_]] = interactionTransitions.flatMap(_.outputEventClasses)

  val allEvents: Set[Class[_]] = sensoryEvents ++ interactionEvents

  val ingredients: Map[String, Class[_]] = ((interactionEvents ++ sensoryEvents).flatMap {
    eventClass =>
      eventClass.getDeclaredFields.toSeq.map(f => f.getName -> f.getType)
  } ++ interactionTransitions.flatMap(_.outputIngredient)).toMap
}
