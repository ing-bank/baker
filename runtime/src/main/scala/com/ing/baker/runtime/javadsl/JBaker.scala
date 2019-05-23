package com.ing.baker.runtime.javadsl

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.akka.{AkkaBaker, ProcessState}
import akka.actor.{ActorSystem, Address}
import akka.stream.Materializer
import cats.data.NonEmptyList
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.akka._
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.types.Value
import com.typesafe.config.Config
import javax.annotation.Nonnull

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.Future

object JBaker {

  def akkaLocalDefault(actorSystem: ActorSystem, materializer: Materializer): JBaker =
    new JBaker(new AkkaBaker(AkkaBakerConfig.localDefault(actorSystem, materializer)))

  def akkaClusterDefault(seedNodes: java.util.List[Address], actorSystem: ActorSystem, materializer: Materializer): JBaker = {
    val nodes =
      if(seedNodes.isEmpty) throw new BakerException("Baker cluster configuration without baker.cluster.seed-nodes")
      else NonEmptyList.fromListUnsafe(seedNodes.asScala.toList)
    new JBaker(new AkkaBaker(AkkaBakerConfig.clusterDefault(nodes, actorSystem, materializer)))
  }

  def akka(config: AkkaBakerConfig): JBaker =
    new JBaker(Baker.akka(config))

  def akka(config: Config, actorSystem: ActorSystem, materializer: Materializer): JBaker =
    new JBaker(Baker.akka(config, actorSystem, materializer))

  def other(baker: Baker) =
    new JBaker(baker)
}

class JBaker private(private val baker: ScalaBaker[Future]) extends JavaBaker[CompletableFuture] {

  override type Result = SensoryEventResult

  override type Moments = SensoryEventMoments

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId.
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipe identifier.
    */
  def addRecipe(@Nonnull compiledRecipe: CompiledRecipe): CompletableFuture[String] =
    toCompletableFuture(baker.addRecipe(compiledRecipe))

  /**
    * Adds a single interaction implementation to baker.
    *
    * @param implementation The implementation that should be added.
    */
  def addImplementation(@Nonnull implementation: AnyRef): CompletableFuture[Unit] =
    toCompletableFuture(baker.addImplementation(implementation))

  /**
    * Adds a single interaction implementation to baker.
    *
    * @param implementation The implementation that should be added.
    */
  def addImplementation(@Nonnull implementation: InteractionImplementation): CompletableFuture[Unit] =
    toCompletableFuture(baker.addImplementation(implementation))

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addImplementations(@Nonnull implementations: java.util.List[AnyRef]): CompletableFuture[Unit] =
    toCompletableFuture(baker.addImplementations(implementations.asScala))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def gracefulShutdown(): CompletableFuture[Unit] =
    toCompletableFuture(baker.gracefulShutdown())

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param processId The process identifier
    */
  def bake(@Nonnull recipeId: String, @Nonnull processId: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.bake(recipeId, processId))

  def fireSensoryEventReceived(processId: String, event: Any, correlationId: String): CompletableFuture[SensoryEventStatus] =
    fireSensoryEventReceived(processId, event, Optional.of(correlationId))

  def fireSensoryEventCompleted(processId: String, event: Any, correlationId: String): CompletableFuture[SensoryEventResult] =
    fireSensoryEventCompleted(processId, event, Optional.of(correlationId))

  def fireSensoryEvent(processId: String, event: Any, correlationId: String): SensoryEventMoments =
    fireSensoryEvent(processId, event, Optional.of(correlationId))

  def fireSensoryEventReceived(processId: String, event: Any): CompletableFuture[SensoryEventStatus] =
    fireSensoryEventReceived(processId, event, Optional.empty[String]())

  def fireSensoryEventCompleted(processId: String, event: Any): CompletableFuture[SensoryEventResult] =
    fireSensoryEventCompleted(processId, event, Optional.empty[String]())

  def fireSensoryEvent(processId: String, event: Any): SensoryEventMoments =
    fireSensoryEvent(processId, event, Optional.empty[String]())

  def fireSensoryEventReceived(processId: String, event: Any, correlationId: Optional[String]): CompletableFuture[SensoryEventStatus] =
    toCompletableFuture(baker.fireSensoryEventReceived(processId, event))

  def fireSensoryEventCompleted(processId: String, event: Any, correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireSensoryEventCompleted(processId, event)).thenApply { result =>
      new SensoryEventResult(
        status = result.status,
        events = result.events.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  def fireSensoryEvent(processId: String, event: Any, correlationId: Optional[String]): SensoryEventMoments = {
    val scalaResult = baker.fireSensoryEvent(processId, event)
    new SensoryEventMoments(
      received = toCompletableFuture(scalaResult.received),
      completed = toCompletableFuture(scalaResult.completed).thenApply { result =>
        new SensoryEventResult(
          status = result.status,
          events = result.events.asJava,
          ingredients = result.ingredients.asJava
        )
      })
  }

  /**
    * Retries a blocked interaction.
    *
    * @param processId       The process identifier.
    * @param interactionName The name of the blocked interaction.
    * @return
    */
  def retryInteraction(@Nonnull processId: String, @Nonnull interactionName: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.retryInteraction(processId, interactionName))

  /**
    * Resolves a blocked interaction by giving it's output.
    *
    * @param processId       The process identifier.
    * @param interactionName The name of the blocked interaction.
    * @param event           The output of the interaction.
    * @return
    */
  def resolveInteraction(@Nonnull processId: String, @Nonnull interactionName: String, @Nonnull event: Any): CompletableFuture[Unit] =
    toCompletableFuture(baker.resolveInteraction(processId, interactionName, event))

  /**
    * Stops a retrying interaction.
    *
    * @param processId       The process identifier.
    * @param interactionName The name of the retrying interaction.
    * @return
    */
  def stopRetryingInteraction(@Nonnull processId: String, @Nonnull interactionName: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.stopRetryingInteraction(processId, interactionName))

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param processId The process identifier
    * @return
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("When no process is deleted")
  def getIngredients(@Nonnull processId: String): CompletableFuture[java.util.Map[String, Value]] =
    toCompletableFutureMap(baker.getIngredients(processId))

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId the recipeId
    * @return The JRecipeInformation recipe
    */
  def getRecipe(@Nonnull recipeId: String): CompletableFuture[RecipeInformation] =
    toCompletableFuture(baker.getRecipe(recipeId))

  /**
    * Return alls recipes added to this Baker
    *
    * @return A map with all recipes from recipeId -> JRecipeInformation
    */
  def getAllRecipes(): CompletableFuture[java.util.Map[String, RecipeInformation]] =
    toCompletableFutureMap(baker.getAllRecipes)

  /**
    * Returns an index of all processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  def getIndex: CompletableFuture[util.Set[ProcessMetadata]] =
    toCompletableFutureSet(baker.getIndex)

  /**
    * Registers a listener to all runtime events for this baker instance.
    *
    * Note that:
    *
    * - The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
    * - The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.
    *
    * Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
    *
    * - logging
    * - metrics
    * - unit tests
    * - ...
    *
    * @param recipeName the name of all recipes this event listener should be triggered for
    * @param listener   The listener to subscribe to events.
    */
  def registerEventListener(@Nonnull recipeName: String, @Nonnull listener: EventListener): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(recipeName, listener))

  /**
    * Registers a listener to all runtime events for this baker instance.
    *
    * Note that:
    *
    * - The delivery guarantee is *AT MOST ONCE*. Practically this means you can miss events when the application terminates (unexpected or not).
    * - The delivery is local (JVM) only, you will NOT receive events from other nodes when running in cluster mode.
    *
    * Because of these constraints you should not use an event listener for critical functionality. Valid use cases might be:
    *
    * - logging
    * - metrics
    * - unit tests
    * - ...
    *
    * @param listener The listener to subscribe to events.
    */
  def registerEventListener(@Nonnull listener: EventListener): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(listener))


  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(@Nonnull processId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(processId, style))

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getProcessState(@Nonnull processId: String): CompletableFuture[ProcessState] =
    toCompletableFuture(baker.getProcessState(processId))

  private def toCompletableFuture[T](scalaFuture: Future[T]): CompletableFuture[T] =
    FutureConverters.toJava(scalaFuture).toCompletableFuture

  private def toCompletableFutureSet[T](scalaFuture: Future[Set[T]]): CompletableFuture[java.util.Set[T]] =
    FutureConverters.toJava(
      scalaFuture)
      .toCompletableFuture
      .thenApply(_.asJava)

  private def toCompletableFutureMap[K, V](scalaFuture: Future[Map[K, V]]): CompletableFuture[java.util.Map[K, V]] =
    FutureConverters.toJava(
      scalaFuture)
      .toCompletableFuture
      .thenApply(_.asJava)

}
