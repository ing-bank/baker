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
import com.ing.baker.runtime.common.SensoryEventStatus
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

class Baker private[runtime](private val baker: scaladsl.Baker) extends common.Baker[CompletableFuture] with JavaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

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
  def addInteractionInstance(@Nonnull implementation: InteractionInstance): CompletableFuture[Unit] =
    toCompletableFuture(baker.addInteractionInstance(implementation.asScala))

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addInteractionInstances(@Nonnull implementations: java.util.List[InteractionInstance]): CompletableFuture[Unit] =
    toCompletableFuture(baker.addInteractionInstances(implementations.asScala.map(_.asScala)))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def gracefulShutdown(): CompletableFuture[Unit] =
    toCompletableFuture(baker.gracefulShutdown())

  /**
    * This bakes (creates) a new process instance of the recipe.
    *
    * @param recipeId  The recipe this instance will be baked for
    * @param recipeInstanceId The process identifier
    */
  def bake(@Nonnull recipeId: String, @Nonnull recipeInstanceId: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.bake(recipeId, recipeInstanceId))

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: String): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.of(correlationId))

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.empty[String]())

  def fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Optional[String]): CompletableFuture[SensoryEventStatus] =
    toCompletableFuture(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event.asScala, Option.apply(correlationId.orElse(null))))

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event.asScala, Option.apply(correlationId.orElse(null)))).thenApply { result =>
      SensoryEventResult(
        sensoryEventStatus = result.sensoryEventStatus,
        eventNames = result.eventNames.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireEventAndResolveOnEvent(recipeInstanceId, event.asScala, onEvent, Option.apply(correlationId.orElse(null)))).thenApply { result =>
      SensoryEventResult(
        sensoryEventStatus = result.sensoryEventStatus,
        eventNames = result.eventNames.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Optional[String]): EventResolutions = {
    val scalaResult = baker.fireEvent(recipeInstanceId, event.asScala)
    EventResolutions(
      resolveWhenReceived = toCompletableFuture(scalaResult.resolveWhenReceived),
      resolveWhenCompleted = toCompletableFuture(scalaResult.resolveWhenCompleted).thenApply { result =>
        SensoryEventResult(
          sensoryEventStatus = result.sensoryEventStatus,
          eventNames = result.eventNames.asJava,
          ingredients = result.ingredients.asJava
        )
      })
  }

  /**
    * Retries a blocked interaction.
    *
    * @param recipeInstanceId       The process identifier.
    * @param interactionName The name of the blocked interaction.
    * @return
    */
  def retryInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.retryInteraction(recipeInstanceId, interactionName))

  /**
    * Resolves a blocked interaction by giving it's output.
    *
    * @param recipeInstanceId       The process identifier.
    * @param interactionName The name of the blocked interaction.
    * @param event           The output of the interaction.
    * @return
    */
  def resolveInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String, @Nonnull event: EventInstance): CompletableFuture[Unit] =
    toCompletableFuture(baker.resolveInteraction(recipeInstanceId, interactionName, event.asScala))

  /**
    * Stops a retrying interaction.
    *
    * @param recipeInstanceId       The process identifier.
    * @param interactionName The name of the retrying interaction.
    * @return
    */
  def stopRetryingInteraction(@Nonnull recipeInstanceId: String, @Nonnull interactionName: String): CompletableFuture[Unit] =
    toCompletableFuture(baker.stopRetryingInteraction(recipeInstanceId, interactionName))

  /**
    * Returns the state of a process instance. This includes the ingredients and names of the events.
    *
    * @param recipeInstanceId The process identifier
    * @return The state of the process instance
    */
  def getRecipeInstanceState(@Nonnull recipeInstanceId: String): CompletableFuture[RecipeInstanceState] =
    toCompletableFuture(baker.getRecipeInstanceState(recipeInstanceId)).thenApply(_.asJava)

  /**
    * Returns all the ingredients that are accumulated for a given process.
    *
    * @param recipeInstanceId The process identifier
    * @return
    */
  def getIngredients(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.Map[String, Value]] =
    toCompletableFutureMap(baker.getIngredients(recipeInstanceId))

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  def getEvents(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.List[EventMoment]] =
    toCompletableFuture(baker.getEvents(recipeInstanceId)).thenApply(_.map(_.asJava()).asJava)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  def getEventNames(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.List[String]] =
    toCompletableFuture(baker.getEventNames(recipeInstanceId)).thenApply(_.asJava)

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId the recipeId
    * @return The JRecipeInformation recipe
    */
  def getRecipe(@Nonnull recipeId: String): CompletableFuture[RecipeInformation] =
    toCompletableFuture(baker.getRecipe(recipeId)).thenApply(_.asJava)

  /**
    * Return alls recipes added to this Baker
    *
    * @return A map with all recipes from recipeId -> JRecipeInformation
    */
  def getAllRecipes: CompletableFuture[java.util.Map[String, RecipeInformation]] =
    FutureConverters.toJava(baker.getAllRecipes).toCompletableFuture.thenApply(_.mapValues(_.asJava).asJava)

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
  def getAllRecipeInstancesMetadata: CompletableFuture[util.Set[RecipeInstanceMetadata]] =
    FutureConverters
      .toJava(baker.getAllRecipeInstancesMetadata)
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
  override def registerEventListener(@Nonnull recipeName: String, @Nonnull listenerFunction: BiConsumer[String, EventInstance]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(recipeName,
      (recipeInstanceId: String, event: scaladsl.EventInstance) => listenerFunction.accept(recipeInstanceId, event.asJava)))


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
  override def registerEventListener(listenerFunction: BiConsumer[String, EventInstance]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(
      (recipeInstanceId: String, event: scaladsl.EventInstance) => listenerFunction.accept(recipeInstanceId, event.asJava)))


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
    baker.registerEventListener((recipeInstanceId: String, runtimeEvent: scaladsl.EventInstance) => eventListener.processEvent(recipeInstanceId, runtimeEvent.asJava))


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
    * @param recipeInstanceId The process identifier
    * @return
    */
  def getVisualState(@Nonnull recipeInstanceId: String): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(recipeInstanceId, RecipeVisualStyle.default))

  /**
    * Returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    *
    * @param recipeInstanceId The process identifier
    * @return
    */
  def getVisualState(@Nonnull recipeInstanceId: String, style: RecipeVisualStyle): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(recipeInstanceId, style))

  private def toCompletableFuture[T](scalaFuture: Future[T]): CompletableFuture[T] =
    FutureConverters.toJava(scalaFuture).toCompletableFuture

  private def toCompletableFutureMap[K, V](scalaFuture: Future[Map[K, V]]): CompletableFuture[java.util.Map[K, V]] =
    FutureConverters.toJava(
      scalaFuture)
      .toCompletableFuture
      .thenApply(_.asJava)

}
