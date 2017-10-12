package com.ing.baker.il

import java.io.{File, IOException}

import com.ing.baker.il.petrinet.{InteractionTransition, Place, RecipePetriNet}
import com.ing.baker.petrinet.api.Marking

import scala.collection.JavaConverters._
import scala.concurrent.duration.Duration

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          petriNet: RecipePetriNet,
                          initialMarking: Marking[Place],
                          sensoryEvents: Set[EventType],
                          validationErrors: Seq[String] = Seq.empty,
                          eventReceivePeriod: Duration,
                          retentionPeriod: Duration) {

  def getValidationErrors: java.util.List[String] = validationErrors.toList.asJava

  /**
    * Visualise the compiled recipe in DOT format
    * @return
    */
  def getRecipeVisualization: String =
    RecipeVisualizer.visualiseCompiledRecipe(this)

  /**
    * Writes the visual recipe as an SVG to a given file.
    */
  @throws[IOException]("When failing to write to the file for any reason")
  def writeVisualRecipeToSVGFile(file: File): Unit = {

    import guru.nidi.graphviz.engine.{Format, Graphviz}
    import guru.nidi.graphviz.parse.Parser

    val g = Parser.read(getRecipeVisualization)
    Graphviz.fromGraph(g).render(Format.SVG).toFile(file)
  }

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

  val interactionEvents: Set[EventType] = interactionTransitions flatMap(it => it.eventsToFire)

  val allEvents: Set[EventType] = sensoryEvents ++ interactionEvents

  val allIngredientsProvidedByEvents: Set[IngredientType] = allEvents.flatMap {
    events => events.ingredientTypes
  }

  val ingredients: Map[String, IngredientType] = allIngredientsProvidedByEvents.map(i => i.name -> i).toMap
}
