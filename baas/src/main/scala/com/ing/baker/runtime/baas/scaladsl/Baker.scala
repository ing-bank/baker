package com.ing.baker.runtime.baas.scaladsl

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.Marshal
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.model.{HttpMethods, HttpRequest, MessageEntity, Uri}
import akka.stream.Materializer
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.akka.actor.serialization.{Encryption, SerializersProvider}
import com.ing.baker.runtime.baas.BaaSProto._
import com.ing.baker.runtime.baas.BaaSProtocol
import com.ing.baker.runtime.baas.MarshallingUtils._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, EventMoment, EventResolutions, InteractionInstance, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult, Baker => ScalaBaker}
import com.ing.baker.types.Value

import scala.concurrent.Future

object Baker {

  def remote(hostname: String, encryption: Encryption = Encryption.NoEncryption)(implicit system: ActorSystem, mat: Materializer) =
    Baker(Uri(hostname), encryption)
}

case class Baker(hostname: Uri, encryption: Encryption = Encryption.NoEncryption)(implicit system: ActorSystem, mat: Materializer) extends ScalaBaker {

  import system.dispatcher

  implicit val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  val root: Path = Path./("api")./("v3")

  def withPath(path: Path): Uri = hostname.withPath(path)

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] =
    for {
      encoded <- Marshal(BaaSProtocol.AddRecipeRequest(compiledRecipe)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("addRecipe")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.AddRecipeResponse](response).withBakerExceptions
    } yield decoded.recipeId

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] =
    for {
      encoded <- Marshal(BaaSProtocol.GetRecipeRequest(recipeId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("getRecipe")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.GetRecipeResponse](response).withBakerExceptions
    } yield decoded.recipeInformation

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = {
    val request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("getAllRecipes")))
    for {
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.GetAllRecipesResponse](response).withBakerExceptions
    } yield decoded.map
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
    for {
      encoded <- Marshal(BaaSProtocol.BakeRequest(recipeId, recipeInstanceId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("bake")), entity = encoded)
      response <- Http().singleRequest(request)
      _ <- unmarshalBakerExceptions(response)
    } yield ()

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] =
    for {
      encoded <- Marshal(BaaSProtocol.FireEventAndResolveWhenReceivedRequest(recipeInstanceId, event, correlationId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("fireEventAndResolveWhenReceived")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.FireEventAndResolveWhenReceivedResponse](response).withBakerExceptions
    } yield decoded.sensoryEventStatus

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventResult] =
    for {
      encoded <- Marshal(BaaSProtocol.FireEventAndResolveWhenCompletedRequest(recipeInstanceId, event, correlationId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("fireEventAndResolveWhenCompleted")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.FireEventAndResolveWhenCompletedResponse](response).withBakerExceptions
    } yield decoded.sensoryEventResult

  /**
    * Notifies Baker that an event has happened and waits until an specific event has executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param onEvent          The name of the event to wait for
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): Future[SensoryEventResult] =
    for {
      encoded <- Marshal(BaaSProtocol.FireEventAndResolveOnEventRequest(recipeInstanceId, event, onEvent, correlationId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("fireEventAndResolveOnEvent")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.FireEventAndResolveOnEventResponse](response).withBakerExceptions
    } yield decoded.sensoryEventResult

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = {
    for {
      encoded <- Marshal(BaaSProtocol.FireEventRequest(recipeInstanceId, event, correlationId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("fireEvent")), entity = encoded)
      response <- Http().singleRequest(request)
      //decoded <- unmarshal(response)[BaaSProtocol.???] TODO f.withBakerExceptionsigure out what to do on this situation with the two futures
    } yield () //decoded.recipeInformation
    ???
  }

  /**
    * Returns an index of all running processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] = {
    val request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("getAllRecipeInstancesMetadata")))
    for {
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.GetAllRecipeInstancesMetadataResponse](response).withBakerExceptions
    } yield decoded.set
  }

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    for {
      encoded <- Marshal(BaaSProtocol.GetRecipeInstanceStateRequest(recipeInstanceId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("getRecipeInstanceState")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.GetRecipeInstanceStateResponse](response).withBakerExceptions
    } yield decoded.recipeInstanceState

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
    getRecipeInstanceState(recipeInstanceId).map(_.ingredients)

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
    getRecipeInstanceState(recipeInstanceId).map(_.events)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): Future[Seq[String]] =
    getRecipeInstanceState(recipeInstanceId).map(_.events.map(_.name))

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): Future[String] =
    for {
      encoded <- Marshal(BaaSProtocol.GetVisualStateRequest(recipeInstanceId)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("getVisualState")), entity = encoded)
      response <- Http().singleRequest(request)
      decoded <- unmarshal[BaaSProtocol.GetVisualStateResponse](response).withBakerExceptions
    } yield decoded.state

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
    throw new NotImplementedError("registerEventListener is not implemented for client bakers")

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
    throw new NotImplementedError("registerEventListener is not implemented for client bakers")

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] =
    throw new NotImplementedError("registerBakerEventListener is not implemented for client bakers")

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation The implementation object
    */
  override def addInteractionInstance(implementation: InteractionInstance): Future[Unit] =
    throw new NotImplementedError("addInteractionInstance is not implemented for client bakers, instances are deployed independently, please view the documentation")

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstances(implementations: Seq[InteractionInstance]): Future[Unit] =
    throw new NotImplementedError("addInteractionInstances is not implemented for client bakers, instances are deployed independently, please view the documentation")

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] =
    throw new NotImplementedError("registerBakerEventListener is not yet implemented for client bakers")

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    for {
      encoded <- Marshal(BaaSProtocol.RetryInteractionRequest(recipeInstanceId, interactionName)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("retryInteraction")), entity = encoded)
      response <- Http().singleRequest(request)
      _ <- unmarshalBakerExceptions(response)
    } yield ()

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
    for {
      encoded <- Marshal(BaaSProtocol.ResolveInteractionRequest(recipeInstanceId, interactionName, event)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("resolveInteraction")), entity = encoded)
      response <- Http().singleRequest(request)
      _ <- unmarshalBakerExceptions(response)
    } yield ()

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
    for {
      encoded <- Marshal(BaaSProtocol.StopRetryingInteractionRequest(recipeInstanceId, interactionName)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("stopRetryingInteraction")), entity = encoded)
      response <- Http().singleRequest(request)
      _ <- unmarshalBakerExceptions(response)
    } yield ()
}
