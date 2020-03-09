package com.ing.baker.baas.scaladsl

import cats.data.EitherT
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.protocol.BaaSProto._
import com.ing.baker.baas.protocol.BaaSProtocol
import com.ing.baker.baas.protocol.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, EventMoment, EventResolutions, InteractionInstance, RecipeEventMetadata, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult, Baker => ScalaBaker}
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.types.Value
import org.http4s.EntityDecoder.collectBinary
import org.http4s.Method._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s._

import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success, Try}

object BakerClient {

  /** Uses the global execution context, which is limited to the amount of available cores in the machine. */
  def bounded(hostname: String): IO[BakerClient] = {
    val ec = ExecutionContext.Implicits.global
    resource(Uri.unsafeFromString(hostname), ec)(IO.contextShift(ec), IO.timer(ec)).use(IO.pure)
  }

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
   * the resulting `IO` is run, each time using the common connection pool.
   */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, BakerClient] = {
    implicit val ev0 = pool
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new BakerClient(_, hostname))
  }
}

final class BakerClient(client: Client[IO], hostname: Uri)(implicit ec: ExecutionContext) extends ScalaBaker {

  val Root = hostname / "api" / "v3"

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] = {
    val request = POST(
      BaaSProtocol.AddRecipeRequest(compiledRecipe),
      Root / "addRecipe"
    )
    handleBakerResponse[BaaSProtocol.AddRecipeResponse, String](request)(_.recipeId)
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] = {
    val request = POST(
      BaaSProtocol.GetRecipeRequest(recipeId),
      Root / "getRecipe"
    )
    handleBakerResponse[BaaSProtocol.GetRecipeResponse, RecipeInformation](request)(_.recipeInformation)
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = {
    val request = GET(
      Root / "getAllRecipes"
    )
    handleBakerResponse[BaaSProtocol.GetAllRecipesResponse, Map[String, RecipeInformation]](request)(_.map)
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] = {
    val request = POST(
      BaaSProtocol.BakeRequest(recipeId, recipeInstanceId),
      Root / "bake"
    )
    handleBakerFailure(request)
  }

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
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] = {
    val request = POST(
      BaaSProtocol.FireEventAndResolveWhenReceivedRequest(recipeInstanceId, event, correlationId),
      Root / "fireEventAndResolveWhenReceived"
    )
    handleBakerResponse[BaaSProtocol.FireEventAndResolveWhenReceivedResponse, SensoryEventStatus](request)(_.sensoryEventStatus)
  }

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
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventResult] = {
    val request = POST(
      BaaSProtocol.FireEventAndResolveWhenCompletedRequest(recipeInstanceId, event, correlationId),
      Root / "fireEventAndResolveWhenCompleted"
    )
    handleBakerResponse[BaaSProtocol.FireEventAndResolveWhenCompletedResponse, SensoryEventResult](request)(_.sensoryEventResult)
  }

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
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): Future[SensoryEventResult] = {
    val request = POST(
      BaaSProtocol.FireEventAndResolveOnEventRequest(recipeInstanceId, event, onEvent, correlationId),
      Root / "fireEventAndResolveOnEvent"
    )
    handleBakerResponse[BaaSProtocol.FireEventAndResolveOnEventResponse, SensoryEventResult](request)(_.sensoryEventResult)
  }

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
    val request = GET(
      Root / "getAllRecipeInstancesMetadata"
    )
    handleBakerResponse[BaaSProtocol.GetAllRecipeInstancesMetadataResponse, Set[RecipeInstanceMetadata]](request)(_.set)
  }

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] = {
    val request = POST(
      BaaSProtocol.GetRecipeInstanceStateRequest(recipeInstanceId),
      Root / "getRecipeInstanceState"
    )
    handleBakerResponse[BaaSProtocol.GetRecipeInstanceStateResponse, RecipeInstanceState](request)(_.recipeInstanceState)
  }

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
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): Future[String] = {
    val request = POST(
      BaaSProtocol.GetVisualStateRequest(recipeInstanceId),
      Root / "getVisualState"
    )
    handleBakerResponse[BaaSProtocol.GetVisualStateResponse, String](request)(_.state)
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    throw new NotImplementedError("registerEventListener is not implemented for client bakers")

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
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
    throw new NotImplementedError("Use the cats.effect.Resource mechanisms for this, you probably don't need to do anything, safe to ignore")

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    val request = POST(
      BaaSProtocol.RetryInteractionRequest(recipeInstanceId, interactionName),
      Root / "retryInteraction"
    )
    handleBakerFailure(request)
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] = {
    val request = POST(
      BaaSProtocol.ResolveInteractionRequest(recipeInstanceId, interactionName, event),
      Root / "resolveInteraction"
    )
    handleBakerFailure(request)
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    val request = POST(
      BaaSProtocol.StopRetryingInteractionRequest(recipeInstanceId, interactionName),
      Root / "stopRetryingInteraction"
    )
    handleBakerFailure(request)
  }

  private type WithBakerException[A] = Either[BaaSProtocol.BaaSRemoteFailure, A]

  private implicit def withBakerExeptionEntityDecoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityDecoder[IO, WithBakerException[A]] =
    EntityDecoder.decodeBy(MediaType.application.`octet-stream`)(collectBinary[IO]).map(_.toArray)
      .flatMapR { bytes =>
        val eitherTry: Try[WithBakerException[A]] =
          baaSRemoteFailureProto.fromByteArray(bytes).map[WithBakerException[A]](Left(_))
            .orElse(protoMap.fromByteArray(bytes).map[WithBakerException[A]](Right(_)))
        eitherTry match {
          case Success(a) =>
            EitherT.fromEither[IO](Right(a))
          case Failure(exception) =>
            EitherT.fromEither[IO](Left(MalformedMessageBodyFailure(exception.getMessage, Some(exception))))
        }
      }

  final class HandleBakerResponsePartial[A, R] {
    def apply[P <: ProtoMessage[P]](request: IO[Request[IO]])(f: A => R)(implicit protoMap: ProtoMap[A, P]): Future[R] =
      client
        .expect[WithBakerException[A]](request)
        .flatMap(_.fold(failure => IO.raiseError(failure.error), IO.pure))
        .map(f)
        .unsafeToFuture()
  }

  private def handleBakerResponse[A, R]: HandleBakerResponsePartial[A, R] = new HandleBakerResponsePartial[A, R]

  private def handleBakerFailure(request: IO[Request[IO]]): Future[Unit] =
    request.flatMap(client.run(_).use(response => response.contentType match {
      case Some(contentType) if contentType.mediaType == MediaType.application.`octet-stream` =>
        EntityDecoder[IO, BaaSProtocol.BaaSRemoteFailure]
          .decode(response, strict = true)
          .value
          .flatMap(_.fold(IO.raiseError(_), e => IO.raiseError(e.error)))
      case _ => IO.unit
    })).unsafeToFuture()
}
