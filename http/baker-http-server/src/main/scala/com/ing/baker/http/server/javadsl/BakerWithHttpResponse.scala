package com.ing.baker.http.server.javadsl

import cats.effect.unsafe.IORuntime
import com.ing.baker.http.server.common.RecipeLoader
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EncodedRecipe, EventInstance}
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.{AddMetaDataRequest, BakeRequest}
import com.typesafe.scalalogging.LazyLogging
import io.circe.Encoder
import io.circe.generic.auto._
import io.circe.parser.parse

import java.nio.charset.Charset
import java.util.concurrent.{CompletableFuture => JFuture}
import java.util.{Optional, UUID}
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ExecutionContext, Future}
import scala.jdk.FutureConverters.FutureOps

/**
 * A wrapper around baker which calls the specified baker instance, and returns the BakerResult according to the bakery protocol.
 * Useful when making your own controller.
 *
 * @param baker baker methods to wrap
 * @param ec    execution context to use
 */
class BakerWithHttpResponse(val baker: Baker, ec: ExecutionContext) extends LazyLogging {
  implicit val executionContext: ExecutionContext = ec

  def appGetAllInteractions: JFuture[String] = baker.getAllInteractions.toBakerResult

  def appGetInteraction(interactionName: String): JFuture[String] = baker.getInteraction(interactionName).toBakerResult

  def appAddRecipe(recipe: String): JFuture[String] = {
    (for {
      json <- parse(recipe).toOption
      encodedRecipe <- json.as[EncodedRecipe].toOption
    } yield RecipeLoader.fromBytes(encodedRecipe.base64.getBytes(Charset.forName("UTF-8"))).unsafeToFuture()(IORuntime.global))
      .map(_.flatMap(recipe => baker.addRecipe(recipe, validate = false).mapToBakerResult))
      .getOrElse(Future.failed(new IllegalStateException("Error adding recipe")))
  }.asJava.toCompletableFuture

  def appGetRecipe(recipeId: String): JFuture[String] = baker.getRecipe(recipeId).toBakerResult

  def appGetAllRecipes: JFuture[String] = baker.getAllRecipes.toBakerResult

  def appGetVisualRecipe(recipeId: String): JFuture[String] = baker.getRecipeVisual(recipeId).toBakerResult

  def bake(recipeId: String, recipeInstanceId: String): JFuture[String] =
    baker.bake(recipeId, recipeInstanceId).toBakerResult

  def bakeWithBakeRequest(recipeId: String, recipeInstanceId: String, bakeRequestJson: String): JFuture[String] =
    baker.bake(recipeId, recipeInstanceId, getMetaDataFromBakeRequest(bakeRequestJson)).toBakerResult

  def bakeWithMetadata(recipeId: String, recipeInstanceId: String, metadata: Map[String, String]): JFuture[String] =
    baker.bake(recipeId, recipeInstanceId, metadata).toBakerResult

  def getMetaDataFromBakeRequest(bakeRequestJson: String): Map[String, String] = {
    parse(bakeRequestJson) match {
      case Left(_) =>
        logger.error("Failure parsing json of bakeRequest")
        Map.empty[String, String]
      case Right(json: io.circe.Json) =>
        json.as[BakeRequest] match {
          case Left(_) =>
            logger.error("Failure parsing bakeRequest")
            Map.empty[String, String]
          case Right(bakeRequest: BakeRequest) =>
            bakeRequest.metadata.getOrElse(Map.empty[String, String])
        }
    }
  }

  def getMetaDataFromAddMetaDataRequest(addMetaDataRequestJson: String): Map[String, String] = {
    parse(addMetaDataRequestJson) match {
      case Left(_) =>
        logger.error("Failure parsing json of AddMetaDataRequest")
        throw BakerException.UnexpectedException("Failure parsing json of AddMetaDataRequest")
      case Right(json: io.circe.Json) =>
        json.as[AddMetaDataRequest] match {
          case Left(_) =>
            logger.error("Failure parsing of AddMetaDataRequest")
            throw BakerException.UnexpectedException("Failure parsing of AddMetaDataRequest")
          case Right(addMetaDataRequest: AddMetaDataRequest) =>
            addMetaDataRequest.metadata
        }
    }
  }

  def parseEventRequest(eventJson: String): Either[BakerException, EventInstance] = {
    parse(eventJson) match {
      case Left(_) =>
        logger.error("Failure parsing of EventInstance")
        Left(BakerException.UnexpectedException("Failure parsing of EventInstance"))
      case Right(json: io.circe.Json) =>
        json.as[EventInstance] match {
          case Left(_) =>
            logger.error("Failure decoding json to EventInstance")
            Left(BakerException.UnexpectedException("Failure decoding json to EventInstance"))
          case Right(eventInstance: EventInstance) =>
            Right(eventInstance)
        }
    }
  }

  def toBakerResult[A](f: Future[A])(implicit encoder: Encoder[A]): Future[String] = {
    f.map {
      case () => BakerResult.Ack
      case a => BakerResult(a)
    }.recover {
      case e: BakerException => BakerResult(e)
      case e: Throwable =>
        val errorId = UUID.randomUUID().toString
        logger.error(s"Unexpected exception happened when calling Baker (id='$errorId').", e)
        BakerResult(BakerException.UnexpectedException(errorId))
    }.map(bakerResultEncoder.apply(_).noSpaces)
  }

  def toBakerResultJFuture[A](f: Future[A])(implicit encoder: Encoder[A]): JFuture[String] = {
    toBakerResult(f)(encoder)
      .asJava
      .toCompletableFuture
  }

  /**
   * Do calls for a specific instance.
   */
  def instance(recipeInstanceId: String): InstanceResponseMapper = new InstanceResponseMapper(recipeInstanceId)

  class InstanceResponseMapper(recipeInstanceId: String) {
    def get(): JFuture[String] = baker.getRecipeInstanceState(recipeInstanceId).toBakerResult

    def hasRecipeInstance: JFuture[String] = baker.hasRecipeInstance(recipeInstanceId).toBakerResult

    def getEvents: JFuture[String] = baker.getEvents(recipeInstanceId).toBakerResult

    def getIngredient(name: String): JFuture[String] = baker.getIngredient(recipeInstanceId, name).toBakerResult

    def getIngredients: JFuture[String] = baker.getIngredients(recipeInstanceId).toBakerResult

    def getVisual: JFuture[String] = baker.getVisualState(recipeInstanceId).toBakerResult

    def fireAndResolveWhenReceived(eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveWhenReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveWhenCompleted(eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveWhenCompleted(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveOnEvent(eventJson: String, event: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveOnEvent(recipeInstanceId, _, event, toOption(maybeCorrelationId)))

    def addMetaData(addMetaDataRequestJson: String): JFuture[String] =
      baker.addMetaData(recipeInstanceId, getMetaDataFromAddMetaDataRequest(addMetaDataRequestJson))
        .toBakerResult

    def retryInteraction(interactionName: String): JFuture[String] =
      baker.retryInteraction(recipeInstanceId, interactionName).toBakerResult

    def stopRetryingInteraction(interactionName: String): JFuture[String] =
      baker.stopRetryingInteraction(recipeInstanceId, interactionName).toBakerResult

    def resolveInteraction(interactionName: String, eventJson: String): JFuture[String] =
      parseEventAndExecute(eventJson, baker.resolveInteraction(recipeInstanceId, interactionName, _))

    def fireAndResolveWhenReceivedFromEventInstance(eventInstance: EventInstance, maybeCorrelationId: Optional[String]): JFuture[String] =
      eventInstanceExecute(eventInstance, baker.fireEventAndResolveWhenReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveWhenCompletedFromEventInstance(eventInstance: EventInstance, maybeCorrelationId: Optional[String]): JFuture[String] =
      eventInstanceExecute(eventInstance, baker.fireEventAndResolveWhenCompleted(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveOnEventFromEventInstance(eventInstance: EventInstance, event: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      eventInstanceExecute(eventInstance, baker.fireEventAndResolveOnEvent(recipeInstanceId, _, event, toOption(maybeCorrelationId)))

    def resolveInteractionFromEventInstance(interactionName: String, eventInstance: EventInstance): JFuture[String] =
      eventInstanceExecute(eventInstance, baker.resolveInteraction(recipeInstanceId, interactionName, _))

    def delete(removeFromIndex: Boolean): JFuture[String] =
      baker.deleteRecipeInstance(recipeInstanceId, removeFromIndex).toBakerResult

    def fireSensoryEventAndAwaitReceived(eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def awaitCompleted(timeout: FiniteDuration): JFuture[String] =
      baker.awaitCompleted(recipeInstanceId, timeout).toBakerResult

    def awaitEvent(eventName: String, timeout: FiniteDuration, waitForNext: Boolean): JFuture[String] =
      baker.awaitEvent(recipeInstanceId, eventName, timeout, waitForNext).toBakerResult
  }

  private def toOption[T](opt: Optional[T]): Option[T] = if (opt.isPresent) Some(opt.get()) else None

  private def eventInstanceExecute[A](eventInstance: EventInstance, f: EventInstance => Future[A])(implicit encoder: Encoder[A]): JFuture[String] =
    f(eventInstance).mapToBakerResultJFuture

  private def parseEventAndExecute[A](eventJson: String, f: EventInstance => Future[A])(implicit encoder: Encoder[A]): JFuture[String] =
    parseEventRequest(eventJson) match {
      case Right(eventInstance: EventInstance) =>
        f(eventInstance).toBakerResult
      case Left(bakerException: BakerException) =>
        Future(bakerResultEncoder.apply(BakerResult(bakerException)).noSpaces)
          .asJava
          .toCompletableFuture
    }

  private implicit class BakerResultHelperJavaFuture[A](f: => Future[A])(implicit encoder: Encoder[A]) {
    def toBakerResult: JFuture[String] = f.mapToBakerResultJFuture
  }

  private implicit class BakerResultHelperScalaFuture[A](f: => Future[A])(implicit encoder: Encoder[A]) {
    def mapToBakerResult(implicit encoder: Encoder[A]): Future[String] =
      toBakerResult(f)(encoder)

    def mapToBakerResultJFuture(implicit encoder: Encoder[A]): JFuture[String] =
      toBakerResultJFuture(f)(encoder)
  }
}
