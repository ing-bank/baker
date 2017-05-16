package com.ing.baker.recipe.javadsl

import com.ing.baker.compiler._
import com.ing.baker.recipe.common.ActionType.SieveAction
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.{Event, InteractionDescriptor, InteractionFailureStrategy, Recipe}

import scala.annotation.varargs
import scala.collection.JavaConverters._
import scala.concurrent.duration
import scala.concurrent.duration.Duration

case class JRecipe(
    override val name: String,
    override val interactionDescriptors: Seq[InteractionDescriptor[_]],
    override val sieveDescriptors: Seq[InteractionDescriptor[_]],
    override val events: Set[Class[_ <: Event]],
    override val defaultFailureStrategy: InteractionFailureStrategy) extends Recipe {

  def this(name: String) = this(name, Seq.empty, Seq.empty, Set.empty, InteractionFailureStrategy.BlockInteraction)

  def getInteractions: java.util.List[InteractionDescriptor[_]] = interactionDescriptors.asJava

  def getSieves: java.util.List[InteractionDescriptor[_]] = sieveDescriptors.asJava

  def getEvents: java.util.List[Class[_ <: Event]] = events.toList.asJava

  def compileRecipe: JCompiledRecipe = JCompiledRecipe(RecipeCompiler.compileRecipe(this))

  /**
    * Adds the interaction to the recipe.
    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
    *
    * @param interactionDesc the interaction to add
    * @return
    */
  def withInteraction(interactionDesc: JInteractionDescriptor[_ <: JInteraction]): JRecipe =
      withInteractions(Seq(interactionDesc): _*)

  /**
    * Adds the interactions to the recipe.
    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
    *
    * @param newInteractionDescriptors The interactions to add
    * @return
    */
  @SafeVarargs
  @varargs
  def withInteractions(newInteractionDescriptors: JInteractionDescriptor[_ <: JInteraction]*): JRecipe =
    copy(interactionDescriptors = newInteractionDescriptors ++ interactionDescriptors)

  /**
    * Adds a sieve function to the recipe.
    *
    * @param sieveDescriptor
    * @return
    */
  def withSieve(sieveDescriptor: JInteractionDescriptor[_ <: JInteraction]): JRecipe =
    withSieves(Seq(sieveDescriptor): _*)

  /**
    * Adds a sieves function to the recipe.
    *
    * @param newSieveDescriptors
    * @return
    */
  @SafeVarargs
  @varargs
  def withSieves(newSieveDescriptors: JInteractionDescriptor[_ <: JInteraction]*): JRecipe = {
    copy(sieveDescriptors = newSieveDescriptors.map(_.withActionType(SieveAction)) ++ sieveDescriptors)
  }

  /**
    * Adds the sensory event to the recipe
    *
    * @param newEvent
    * @return
    */
  def withSensoryEvent(newEvent: Class[_ <: Event]): JRecipe =
    copy(events = events + newEvent)

  /**
    * Adds the sensory events to the recipe
    *
    * @param eventsToAdd
    * @return
    */
  @SafeVarargs
  @varargs
  def withSensoryEvents(eventsToAdd: Class[_ <: Event]*): JRecipe =
    copy(events = events ++ eventsToAdd)

  /**
    * This actives the incremental backup retry strategy for all the interactions if failure occurs
    * @param initialDelay the initial delay before the first retry starts
    * @param deadline the deadline for how long the retry should run
    * @return
    */
  def withDefaultRetryFailureStrategy(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration): JRecipe =
    copy(
      defaultFailureStrategy =
        RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
          Duration(deadline.toMillis, duration.MILLISECONDS)))

  /**
    * This actives the incremental backup retry strategy for all the interactions if failure occurs
    * @param initialDelay the initial delay before the first retry starts
    * @param backoffFactor the backoff factor for the retry
    * @param maximumRetries the maximum ammount of retries.
    * @return
    */
  def withDefaultRetryFailureStrategy(initialDelay: java.time.Duration,
                                      backoffFactor: Double,
                                      maximumRetries: Int): JRecipe =
  copy(
      defaultFailureStrategy =
        RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
          backoffFactor,
          maximumRetries))

}
