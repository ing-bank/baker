//package com.ing.baker.newrecipe.javadsl
//
//import com.ing.baker.newrecipe.common
//import com.ing.baker.newrecipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
//import com.ing.baker.newrecipe.common._
//
//import scala.annotation.varargs
//import scala.collection.JavaConverters._
//import scala.concurrent.duration
//import scala.concurrent.duration.Duration
//
//case class Recipe(
//    override val name: String,
//    override val interactions: Seq[InteractionDescriptor],
//    override val sieves: Seq[InteractionDescriptor],
//    override val events: Set[Event],
//    override val defaultFailureStrategy: InteractionFailureStrategy) extends common.Recipe {
//
//  def this(name: String) = this(name, Seq.empty, Seq.empty, Set.empty, InteractionFailureStrategy.BlockInteraction)
//
//  def getInteractions: java.util.List[InteractionDescriptor] = interactions.asJava
//
//  def getSieves: java.util.List[InteractionDescriptor] = sieves.asJava
//
//  def getEvents: java.util.List[Event] = events.toList.asJava
//
//  //TODO move this to the recipeCompiler since the recipeDSL is not able to compile itself
////  def compileRecipe: JCompiledRecipe = JCompiledRecipe(RecipeCompiler.compileRecipe(this))
//
//  /**
//    * Adds the interaction to the recipe.
//    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
//    *
//    * @param newInteraction the interaction to add
//    * @return
//    */
//  def withInteraction(newInteraction: InteractionDescriptor): Recipe =
//      withInteractions(Seq(newInteraction): _*)
//
//  /**
//    * Adds the interactions to the recipe.
//    * To get a JInteractionDescriptor from a JInteraction call the of method on JInteractionDescriptor
//    *
//    * @param newInteractions The interactions to add
//    * @return
//    */
//  @SafeVarargs
//  @varargs
//  def withInteractions(newInteractions: InteractionDescriptor*): Recipe =
//    copy(interactions = newInteractions ++ interactions)
//
//  /**
//    * Adds a sieve function to the recipe.
//    *
//    * @param sieveDescriptor
//    * @return
//    */
//  def withSieve(sieveDescriptor: InteractionDescriptor): Recipe =
//    withSieves(Seq(sieveDescriptor): _*)
//
//  /**
//    * Adds a sieves function to the recipe.
//    *
//    * @param newSieves
//    * @return
//    */
//  @SafeVarargs
//  @varargs
//  def withSieves(newSieves: InteractionDescriptor*): Recipe = {
//    copy(sieves = sieves ++ newSieves)
//  }
//
//  /**
//    * Adds the sensory event to the recipe
//    *
//    * @param newEvent
//    * @return
//    */
////  def withSensoryEvent(newEvent: Class[_ <: Event]): Recipe =
////    copy(events = events + newEvent.map(Event()))
//
//  /**
//    * Adds the sensory events to the recipe
//    *
//    * @param eventsToAdd
//    * @return
//    */
//  @SafeVarargs
//  @varargs
//  def withSensoryEvents(eventsToAdd: Class[_ <: Event]*): Recipe =
//    copy(events = events ++ eventsToAdd)
//
//  /**
//    * This actives the incremental backup retry strategy for all the interactions if failure occurs
//    * @param initialDelay the initial delay before the first retry starts
//    * @param deadline the deadline for how long the retry should run
//    * @return
//    */
//  def withDefaultRetryFailureStrategy(initialDelay: java.time.Duration,
//                                      deadline: java.time.Duration): Recipe =
//    copy(
//      defaultFailureStrategy =
//        RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
//          Duration(deadline.toMillis, duration.MILLISECONDS)))
//
//  /**
//    * This actives the incremental backup retry strategy for all the interactions if failure occurs
//    * @param initialDelay the initial delay before the first retry starts
//    * @param backoffFactor the backoff factor for the retry
//    * @param maximumRetries the maximum ammount of retries.
//    * @return
//    */
//  def withDefaultRetryFailureStrategy(initialDelay: java.time.Duration,
//                                      backoffFactor: Double,
//                                      maximumRetries: Int): Recipe =
//  copy(
//      defaultFailureStrategy =
//        RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
//          backoffFactor,
//          maximumRetries))
//
//}
