package com.ing.baker.java_api

import com.ing.baker.compiler.CompiledRecipe

import com.ing.baker.RecipeVisualizer._

import scala.collection.JavaConverters._

/**
  * A class that can give information about a compiled recipe.
  *
  * @param compiledRecipe
  */
case class JCompiledRecipe private(private val compiledRecipe: CompiledRecipe) {

  def getValidationErrors(): java.util.List[String] =
    compiledRecipe.validationErrors
      .filterNot(_.contains("No implementation provided for interaction:"))
      .toList
      .asJava

  /**
    * Returns a DOT (http://www.graphviz.org/) representation of the recipe.
    * @return
    */
  def getRecipeVisualization(): String = compiledRecipe.getRecipeVisualization

  /**
    * Return a visualization of the petri net that is created from the recipe.
    * @return
    */
  def getPetriNetVisualization(): String = compiledRecipe.getPetriNetVisualization

  /**
    * Returns a DOT (http://www.graphviz.org/) representation of the recipe.
    * All events/interaction/ingredients that contain the given filter string are filtered out
    * @param filter
    * @return
    */
  def getFilteredRecipeVisualization(filter: String): String =
    compiledRecipe.petriNet.innerGraph.toDot(x => !x.contains(filter))

  /**
    * Returns a DOT (http://www.graphviz.org/) representation of the recipe.
    * All events/interaction/ingredients that contain one of the given filter strings are filtered out
    * @param filters
    * @return
    */
  def getFilteredRecipeVisualization(filters: Array[String]): String =
    compiledRecipe.petriNet.innerGraph.toDot((current) =>
      filters.forall(filter => !current.contains(filter)))
}
