package com.ing.baker.runtime.javadsl

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import java.util.function.{BiConsumer, Consumer}

import akka.actor.{ActorSystem, Address}
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.NonEmptyList
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.akka.{AkkaBaker, _}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.common.{RecipeInformation, SensoryEventStatus}
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value
import com.typesafe.config.Config
import javax.annotation.Nonnull

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.Future

object Baker {

  def akkaLocalDefault(actorSystem: ActorSystem, materializer: Materializer): Baker =
    new Baker(new AkkaBaker(AkkaBakerConfig.localDefault(actorSystem, materializer)))

  def akkaClusterDefault(seedNodes: java.util.List[Address], actorSystem: ActorSystem, materializer: Materializer): Baker = {
    val nodes =
      if (seedNodes.isEmpty) throw new IllegalStateException("Baker cluster configuration without baker.cluster.seed-nodes")
      else NonEmptyList.fromListUnsafe(seedNodes.asScala.toList)
    new Baker(new AkkaBaker(AkkaBakerConfig.clusterDefault(nodes, actorSystem, materializer)))
  }

  def akka(config: AkkaBakerConfig): Baker =
    new Baker(scaladsl.Baker.akka(config))

  def akka(config: Config, actorSystem: ActorSystem, materializer: Materializer): Baker =
    new Baker(scaladsl.Baker.akka(config, actorSystem, materializer))

  def akka(config: Config, actorSystem: ActorSystem): Baker =
    new Baker(scaladsl.Baker.akka(config, actorSystem, ActorMaterializer.create(actorSystem)))

  def other(baker: scaladsl.Baker) =
    new Baker(baker)
}

class Baker private(private val baker: scaladsl.Baker) extends common.Baker[CompletableFuture] with JavaApi {

  override type Result = SensoryEventResult

  override type Moments = SensoryEventMoments

  override type Event = RuntimeEvent

  override type PState = ProcessState

  override type Interaction = InteractionImplementation

  override type BakerEventType = BakerEvent

  override type ProcessMetadataType = ProcessMetadata

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
  def addImplementation(@Nonnull implementation: InteractionImplementation): CompletableFuture[Unit] =
    toCompletableFuture(baker.addImplementation(implementation.asScala))

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addImplementations(@Nonnull implementations: java.util.List[InteractionImplementation]): CompletableFuture[Unit] =
    toCompletableFuture(baker.addImplementations(implementations.asScala.map(_.asScala)))

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

  def fireSensoryEventReceived(processId: String, event: RuntimeEvent, correlationId: String): CompletableFuture[SensoryEventStatus] =
    fireSensoryEventReceived(processId, event, Optional.of(correlationId))

  def fireSensoryEventCompleted(processId: String, event: RuntimeEvent, correlationId: String): CompletableFuture[SensoryEventResult] =
    fireSensoryEventCompleted(processId, event, Optional.of(correlationId))

  def fireSensoryEvent(processId: String, event: RuntimeEvent, correlationId: String): SensoryEventMoments =
    fireSensoryEvent(processId, event, Optional.of(correlationId))

  def fireSensoryEventReceived(processId: String, event: RuntimeEvent): CompletableFuture[SensoryEventStatus] =
    fireSensoryEventReceived(processId, event, Optional.empty[String]())

  def fireSensoryEventCompleted(processId: String, event: RuntimeEvent): CompletableFuture[SensoryEventResult] =
    fireSensoryEventCompleted(processId, event, Optional.empty[String]())

  def fireSensoryEvent(processId: String, event: RuntimeEvent): SensoryEventMoments =
    fireSensoryEvent(processId, event, Optional.empty[String]())

  def fireSensoryEventReceived(processId: String, event: RuntimeEvent, correlationId: Optional[String]): CompletableFuture[SensoryEventStatus] =
    toCompletableFuture(baker.fireSensoryEventReceived(processId, event.asScala, Option.apply(correlationId.orElse(null))))

  def fireSensoryEventCompleted(processId: String, event: RuntimeEvent, correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireSensoryEventCompleted(processId, event.asScala, Option.apply(correlationId.orElse(null)))).thenApply { result =>
      new SensoryEventResult(
        status = result.status,
        events = result.events.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  def fireSensoryEvent(processId: String, event: RuntimeEvent, correlationId: Optional[String]): SensoryEventMoments = {
    val scalaResult = baker.fireSensoryEvent(processId, event.asScala)
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
  def resolveInteraction(@Nonnull processId: String, @Nonnull interactionName: String, @Nonnull event: RuntimeEvent): CompletableFuture[Unit] =
    toCompletableFuture(baker.resolveInteraction(processId, interactionName, event.asScala))

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
  def getAllRecipes: CompletableFuture[java.util.Map[String, RecipeInformation]] =
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
  def getAllProcessesMetadata: CompletableFuture[util.Set[ProcessMetadata]] =
    FutureConverters
      .toJava(baker.getAllProcessesMetadata)
      .toCompletableFuture
      .thenApply(_.map(_.asJava).asJava)

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
    * @param listenerFunction   The listener to subscribe to events.
    */
  override def registerEventListener(@Nonnull recipeName: String, @Nonnull listenerFunction: BiConsumer[String, RuntimeEvent]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(recipeName,
      (processId: String, event: scaladsl.RuntimeEvent) => listenerFunction.accept(processId, event.asJava)))


  /**
    * Registers a listener function to all runtime events for this baker instance.
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
    * @param listenerFunction The listener function that is called once these events occur
    */
  override def registerEventListener(listenerFunction: BiConsumer[String, RuntimeEvent]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(
      (processId: String, event: scaladsl.RuntimeEvent) => listenerFunction.accept(processId, event.asJava)))


  /**
    * Registers a listener function to all runtime events for this baker instance.
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
    * @param eventListener The EventListener class the processEvent will be called once these events occur
    */
  @deprecated(message = "Replaced with the consumer function variant", since = "3.0.0")
  def registerEventListener(eventListener: EventListener): Future[Unit] =
    baker.registerEventListener((processId: String, runtimeEvent: scaladsl.RuntimeEvent) => eventListener.processEvent(processId, runtimeEvent.asJava))


  /**
    * Registers a listener that listens to all Baker events
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: Consumer[BakerEvent]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerBakerEventListener((event: scaladsl.BakerEvent) => listenerFunction.accept(event.asJava())))


  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  def getVisualState(@Nonnull processId: String): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(processId, RecipeVisualStyle.default))

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param processId The process identifier
    * @return
    */
  def getVisualState(@Nonnull processId: String, style: RecipeVisualStyle): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(processId, style))

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param processId The process identifier
    * @return The state of the process instance
    */
  def getProcessState(@Nonnull processId: String): CompletableFuture[ProcessState] =
    toCompletableFuture(baker.getProcessState(processId)).thenApply(_.asJava)

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
