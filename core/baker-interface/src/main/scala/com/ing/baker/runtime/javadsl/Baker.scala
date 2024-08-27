package com.ing.baker.runtime.javadsl

import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.common.{RecipeRecord, SensoryEventStatus}
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import java.util.function.{BiConsumer, Consumer}
import javax.annotation.Nonnull
import scala.annotation.nowarn
import scala.jdk.CollectionConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class Baker(private val baker: scaladsl.Baker) extends common.Baker[CompletableFuture] with JavaApi with AutoCloseable {

  /**
    * Get underlying baker instance, which provides the scala api.
    */
  def getScalaBaker: scaladsl.Baker = baker

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type InteractionInstanceDescriptorType = InteractionInstanceDescriptor

  override type IngredientInstanceType = IngredientInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override type InteractionExecutionResultType = InteractionExecutionResult

  override def close(): Unit = {
    Await.result(baker.gracefulShutdown(), 10.seconds)
  }

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId.
    *
    * @param recipeRecord The RecipeRecord recipe.
    * @return A recipe identifier.
    */
  def addRecipe(@Nonnull recipeRecord: RecipeRecord): CompletableFuture[String] =
    toCompletableFuture(baker.addRecipe(recipeRecord))


  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe, timeCreated: Long, validate: Boolean): CompletableFuture[String] = addRecipe(RecipeRecord.of(compiledRecipe, updated = timeCreated, validate = validate))

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe, validate: Boolean): CompletableFuture[String] = addRecipe(compiledRecipe, System.currentTimeMillis(), validate)

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

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    * This variant also gets a metadata map added on bake.
    * This is similar to calling addMetaData after doing the regular bake but depending on the implementation this can be more optimized.
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @param metadata
    * @return
    */
  def bake(recipeId: String, recipeInstanceId: String, metadata: util.Map[String, String]): CompletableFuture[Unit] = {
    toCompletableFuture(baker.bake(recipeId, recipeInstanceId, metadata.asScala.toMap))
  }


  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String, @Nonnull correlationId: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.of(correlationId))

  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: String): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.of(correlationId))

  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): CompletableFuture[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String): CompletableFuture[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Optional.empty[String]())

  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance): EventResolutions =
    fireEvent(recipeInstanceId, event, Optional.empty[String]())

  def fireEventAndResolveWhenReceived(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventStatus] =
    toCompletableFuture(baker.fireEventAndResolveWhenReceived(recipeInstanceId, event.asScala, Option.apply(correlationId.orElse(null))))

  @nowarn
  def fireEventAndResolveWhenCompleted(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireEventAndResolveWhenCompleted(recipeInstanceId, event.asScala, Option.apply(correlationId.orElse(null)))).thenApply { result =>
      SensoryEventResult(
        sensoryEventStatus = result.sensoryEventStatus,
        eventNames = result.eventNames.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  @nowarn
  def fireEventAndResolveOnEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull onEvent: String, @Nonnull correlationId: Optional[String]): CompletableFuture[SensoryEventResult] =
    toCompletableFuture(baker.fireEventAndResolveOnEvent(recipeInstanceId, event.asScala, onEvent, Option.apply(correlationId.orElse(null)))).thenApply { result =>
      SensoryEventResult(
        sensoryEventStatus = result.sensoryEventStatus,
        eventNames = result.eventNames.asJava,
        ingredients = result.ingredients.asJava
      )
    }

  @nowarn
  def fireEvent(@Nonnull recipeInstanceId: String, @Nonnull event: EventInstance, @Nonnull correlationId: Optional[String]): EventResolutions = {
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
    * @param recipeInstanceId The recipeInstance Id.
    * @param name The name of the ingredient.
    *  @return The provided ingredients.
    */
  override def getIngredient(recipeInstanceId: String, name: String): CompletableFuture[Value] =
    toCompletableFuture(baker.getIngredient(recipeInstanceId, name))

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
  @nowarn
  def getEvents(@Nonnull recipeInstanceId: String): CompletableFuture[java.util.List[EventMoment]] =
    toCompletableFuture(baker.getEvents(recipeInstanceId)).thenApply(_.map(_.asJava()).asJava)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  @nowarn
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


  def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): CompletableFuture[String] =
    toCompletableFuture(baker.getRecipeVisual(recipeId))

  /**
    * Return alls recipes added to this Baker
    *
    * @return A map with all recipes from recipeId -> JRecipeInformation
    */
  @nowarn
  def getAllRecipes: CompletableFuture[java.util.Map[String, RecipeInformation]] =
    FutureConverters.toJava(baker.getAllRecipes).toCompletableFuture.thenApply(_.view.map { case (key, value) => (key, value.asJava)}.toMap.asJava)

  @nowarn
  def getInteraction(interactionName: String): CompletableFuture[Optional[InteractionInstanceDescriptorType]] =
    FutureConverters
      .toJava(baker.getInteraction(interactionName))
      .toCompletableFuture
      .thenApply(e => Optional.ofNullable(e.map(_.asJava()).orNull))

  @nowarn
  def getAllInteractions: CompletableFuture[java.util.List[InteractionInstanceDescriptorType]] =
    FutureConverters
      .toJava(baker.getAllInteractions)
      .toCompletableFuture
      .thenApply(_.map(_.asJava()).asJava)

  @nowarn
  def executeSingleInteraction(interactionId: String, ingredients: util.List[IngredientInstanceType]): CompletableFuture[InteractionExecutionResult] =
    FutureConverters
      .toJava(baker.executeSingleInteraction(interactionId, ingredients.asScala.map(_.asScala).toIndexedSeq))
      .toCompletableFuture
      .thenApply(_.asJava)

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
  @nowarn
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
  override def registerEventListener(@Nonnull recipeName: String, @Nonnull listenerFunction: BiConsumer[RecipeEventMetadata, String]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(recipeName,
      (recipeEventMetadata: scaladsl.RecipeEventMetadata, event: String) => listenerFunction.accept(recipeEventMetadata.asJava, event)))

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
  override def registerEventListener(@Nonnull listenerFunction: BiConsumer[RecipeEventMetadata, String]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerEventListener(
      (recipeEventMetadata: scaladsl.RecipeEventMetadata, event: String) => listenerFunction.accept(recipeEventMetadata.asJava, event)))

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
  def registerEventListener(@Nonnull eventListener: EventListener): Future[Unit] =
    baker.registerEventListener((recipeEventMetadata: scaladsl.RecipeEventMetadata, event: String) =>
      eventListener.processEvent(recipeEventMetadata.recipeInstanceId, event))

  /**
    * Registers a listener that listens to all Baker events
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(@Nonnull listenerFunction: Consumer[BakerEvent]): CompletableFuture[Unit] =
    toCompletableFuture(baker.registerBakerEventListener((event: scaladsl.BakerEvent) => listenerFunction.accept(event.asJava)))


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
  def getVisualState(@Nonnull recipeInstanceId: String, @Nonnull style: RecipeVisualStyle): CompletableFuture[String] =
    toCompletableFuture(baker.getVisualState(recipeInstanceId, style))

  @nowarn
  private def toCompletableFuture[T](@Nonnull scalaFuture: Future[T]): CompletableFuture[T] =
    FutureConverters.toJava(scalaFuture).toCompletableFuture

  @nowarn
  private def toCompletableFutureMap[K, V](@Nonnull scalaFuture: Future[Map[K, V]]): CompletableFuture[java.util.Map[K, V]] =
    FutureConverters.toJava(
      scalaFuture)
      .toCompletableFuture
      .thenApply(_.asJava)

  /**
    * This method is used to add metadata to your request. This will be added to the ingredients map in Baker.
    * Since this is meant to be used as metadata this should not
    * These cannot be ingredients already found in your recipe.
    *
    * @param metadata
    */
  override def addMetaData(recipeInstanceId: String, metadata: java.util.Map[String, String]): CompletableFuture[Unit] = {
    val x: Map[String, String] = metadata.asScala.toMap
    toCompletableFuture(baker.addMetaData(recipeInstanceId, x))
  }
}
