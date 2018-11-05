package com.ing.baker.il

import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place, RecipePetriNet}
import com.ing.baker.petrinet.api.Marking

import scala.collection.JavaConverters._
import scala.concurrent.duration.FiniteDuration

object CompiledRecipe {

  def apply(name: String, petriNet: RecipePetriNet, initialMarking: Marking[Place], validationErrors: Seq[String],
            eventReceivePeriod: Option[FiniteDuration], retentionPeriod: Option[FiniteDuration]): CompiledRecipe = {
    /**
      * This calculates a SHA-256 hash for a deterministic string representation of the recipe.
      *
      * For the purpose of data integrity it is enough to truncate to 64 bits:
      *
      * - It is acceptable to truncate in SHA-2 hashes (SHA384 is officially defined as a truncated SHA512)
      *
      * - According to the Birthday Problem, as long as the number of keys is significantly less then 2 32
      * then you need not worry about collisions.
      *
      * Also see the collision table at: https://en.wikipedia.org/wiki/Birthday_attack
      *
      * For example, there is a 1 in a million change of collision when number of recipes reach 6 million
      */
    def calculateRecipeId(): String = {
      val petriNetId: String = petriNet.places.toList.sortBy(_.id).mkString +
        petriNet.transitions.toList.sortBy(_.id).mkString

      val initMarkingId: String = initialMarking.toList.sortBy {
        case (place, _) => place.id
      }.map {
        case (_, tokens) => tokens.toList.sortBy {
          case (tokenData: String, _) => tokenData
          case _ => throw new UnsupportedOperationException("Only string tokens are supported")
        }
      }.toString

      val recipeString = StringBuilder.newBuilder +
        name +
        petriNetId +
        initMarkingId +
        validationErrors.mkString +
        eventReceivePeriod.toString + retentionPeriod

      // truncate to 64 bits = 16 hex chars
      zeroPaddedSHA256(recipeString).substring(0, 16)
    }

    // the recipe id is a hexadecimal format of the hashcode
    val recipeId = calculateRecipeId()
    CompiledRecipe(name, recipeId, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod)
  }
}

/**
  * A Compiled recipe.
  */
case class CompiledRecipe(name: String,
                          recipeId: String,
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
    *
    * @return
    */
  def getRecipeVisualization: String =
    RecipeVisualizer.visualizeRecipe(this)

  /**
    * Visualise the compiled recipe in DOT format
    *
    * @param filterFunc
    * @return
    */
  def getFilteredRecipeVisualization(filterFunc: String => Boolean): String =
    RecipeVisualizer.visualizeRecipe(this, filter = filterFunc)


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
    *
    * @return
    */
  def getPetriNetVisualization: String = RecipeVisualizer.visualizePetriNet(petriNet.innerGraph)

  val interactionTransitions: Set[InteractionTransition] = petriNet.transitions.collect {
    case t: InteractionTransition => t
  }

  val interactionEvents: Set[EventDescriptor] = interactionTransitions flatMap (it => it.eventsToFire)

  val allEvents: Set[EventDescriptor] = sensoryEvents ++ interactionEvents

  def getAllEvents: java.util.Set[EventDescriptor] = allEvents.asJava

  val allIngredients: Set[IngredientDescriptor] = allEvents.flatMap {
    events => events.ingredients
  }

  def getAllIngredients: java.util.Set[IngredientDescriptor] = allIngredients.asJava
}
