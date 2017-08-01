package com.ing.baker.recipe.javadsl

import java.util.Optional

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common._

import scala.annotation.varargs
import scala.collection.JavaConverters._
import scala.concurrent.duration
import scala.concurrent.duration.Duration

case class Recipe(
    override val name: String,
    override val interactions: Seq[common.InteractionDescriptor],
    override val sieves: Seq[common.InteractionDescriptor],
    override val sensoryEvents: Set[common.Event],
    override val defaultFailureStrategy: InteractionFailureStrategy) extends common.Recipe {

  def this(name: String) = this(name, Seq.empty, Seq.empty, Set.empty, InteractionFailureStrategy.BlockInteraction)

  def getInteractions: java.util.List[common.InteractionDescriptor] = interactions.asJava

  def getSieves: java.util.List[common.InteractionDescriptor] = sieves.asJava

  def getEvents: java.util.List[common.Event] = sensoryEvents.toList.asJava

  /**
    * This adds all interactions and sieves of the recipe to this recipe
    * Sensory Events are not added and are expected to be given by the recipe itself
    * @param recipe
    * @return
    */
  def withRecipe(recipe: common.Recipe) = {
    copy(interactions = interactions ++ recipe.interactions, sieves = sieves ++ recipe.sieves)
  }

  /**
    * Adds the interaction to the recipe.
    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
    *
    * @param newInteraction the interaction to add
    * @return
    */
  def withInteraction(newInteraction: common.InteractionDescriptor): Recipe =
      withInteractions(Seq(newInteraction): _*)

  /**
    * Adds the interactions to the recipe.
    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
    *
    * @param newInteractions The interactions to add
    * @return
    */
  @SafeVarargs
  @varargs
  def withInteractions(newInteractions: common.InteractionDescriptor*): Recipe =
    copy(interactions = interactions ++ newInteractions)

  /**
    * Adds a sieve function to the recipe.
    *
    * @param sieveDescriptor
    * @return
    */
  def withSieve(sieveDescriptor: common.InteractionDescriptor): Recipe =
    withSieves(Seq(sieveDescriptor.asInstanceOf[InteractionDescriptor]): _*)

  /**
    * Adds a sieves function to the recipe.
    *
    * @param newSieves
    * @return
    */
  @SafeVarargs
  @varargs
  def withSieves(newSieves: common.InteractionDescriptor*): Recipe = {
    copy(sieves = sieves ++ newSieves)
  }

  /**
    * Adds the sensory event to the recipe
    *
    * @param newEvent
    * @return
    */
  def withSensoryEvent(newEvent: Class[_]): Recipe =
    withSensoryEvents(newEvent)

  /**
    * Adds the sensory event to the recipe
    *
    * @param newEvent
    * @param maxFiringLimit
    * @return
    */
  def withSensoryEvent(newEvent: Class[_], maxFiringLimit: Integer): Recipe =
    copy(sensoryEvents = sensoryEvents + eventClassToCommonEvent(newEvent, Some(maxFiringLimit)))

  /**
    * Adds the sensory events to the recipe
    *
    * @param eventsToAdd
    * @return
    */
  @SafeVarargs
  @varargs
  def withSensoryEvents(eventsToAdd: Class[_]*): Recipe =
    copy(sensoryEvents = sensoryEvents ++ eventsToAdd.map(eventClassToCommonEvent(_, Some(1))))

  /**
    * Adds the sensory event to the recipe with firing limit set to unlimited
    *
    * @param newEvent
    * @return
    */
  def withSensoryEventNoFiringLimit(newEvent: Class[_]): Recipe =
    withSensoryEventsNoFiringLimit(newEvent)


  /**
    * Adds the sensory events to the recipe with firing limit set to unlimited
    *
    * @param eventsToAdd
    * @return
    */
  @SafeVarargs
  @varargs
  def withSensoryEventsNoFiringLimit(eventsToAdd: Class[_]*): Recipe =
  copy(sensoryEvents = sensoryEvents ++ eventsToAdd.map(eventClassToCommonEvent(_, None)))


  /**
    * This actives the incremental backup retry strategy for all the interactions if failure occurs
    * @param initialDelay the initial delay before the first retry starts
    * @param deadline the deadline for how long the retry should run
    * @return
    */
  def withDefaultRetryFailureStrategy(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration): Recipe =
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
                                      maximumRetries: Int): Recipe =
  copy(
      defaultFailureStrategy =
        RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
          backoffFactor,
          maximumRetries))

}
