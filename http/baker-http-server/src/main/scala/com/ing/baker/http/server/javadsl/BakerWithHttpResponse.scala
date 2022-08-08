package com.ing.baker.http.server.javadsl

import com.ing.baker.http.server.common.RecipeLoader
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{Baker, BakerResult, EncodedRecipe, EventInstance}
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.typesafe.scalalogging.LazyLogging
import io.circe.Encoder
import io.circe.generic.auto._
import io.circe.parser.parse

import java.nio.charset.Charset
import java.util.concurrent.{CompletableFuture => JFuture}
import java.util.{Optional, UUID}
import scala.compat.java8.FutureConverters.FutureOps
import scala.concurrent.{ExecutionContext, Future}

/**
  * A wrapper around baker which calls the specified baker instance, and returns the BakerResult according to the bakery protocol.
  * Useful when making your own controller.
  *
  * @param baker baker methods to wrap
  * @param ec execution context to use
  */
class BakerWithHttpResponse(val baker: Baker, ec: ExecutionContext) extends LazyLogging {
  implicit val executionContext: ExecutionContext = ec

  def appGetAllInteractions: JFuture[String] = baker.getAllInteractions.toBakerResult

  def appGetInteraction(interactionName: String): JFuture[String] = baker.getInteraction(interactionName).toBakerResult

  def appAddRecipe(recipe: String): JFuture[String] = {
    (for {
      json <- parse(recipe).toOption
      encodedRecipe <- json.as[EncodedRecipe].toOption
    } yield RecipeLoader.fromBytes(encodedRecipe.base64.getBytes(Charset.forName("UTF-8"))).unsafeToFuture())
      .map(_.flatMap(recipe => baker.addRecipe(recipe, validate = false).toBakerResultScalaFuture))
      .getOrElse(Future.failed(new IllegalStateException("Error adding recipe")))
  }.toJava.toCompletableFuture

  def appGetRecipe(recipeId: String): JFuture[String] = baker.getRecipe(recipeId).toBakerResult

  def appGetAllRecipes: JFuture[String] = baker.getAllRecipes.toBakerResult

  def appGetVisualRecipe(recipeId: String): JFuture[String] = baker.getRecipeVisual(recipeId).toBakerResult

  def bake(recipeId: String, recipeInstanceId: String): JFuture[String] = baker.bake(recipeId, recipeInstanceId).toBakerResult

  /**
    * Do calls for a specific instance.
    */
  def instance(recipeInstanceId: String) : InstanceResponseMapper = new InstanceResponseMapper(recipeInstanceId)

  class InstanceResponseMapper(recipeInstanceId: String) {
    def get(): JFuture[String] =  baker.getRecipeInstanceState(recipeInstanceId).toBakerResult

    def getEvents: JFuture[String] = baker.getEvents(recipeInstanceId).toBakerResult

    def getIngredients: JFuture[String] = baker.getIngredients(recipeInstanceId).toBakerResult

    def getVisual: JFuture[String] = baker.getVisualState(recipeInstanceId).toBakerResult

    def fireAndResolveWhenReceived(eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveWhenReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveWhenCompleted(eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveWhenCompleted(recipeInstanceId, _, toOption(maybeCorrelationId)))

    def fireAndResolveOnEvent(eventJson: String, event: String, maybeCorrelationId: Optional[String]): JFuture[String] =
      parseEventAndExecute(eventJson, baker.fireEventAndResolveOnEvent(recipeInstanceId, _, event, toOption(maybeCorrelationId)))

    def retryInteraction(interactionName: String): JFuture[String] =
      baker.retryInteraction(recipeInstanceId, interactionName).toBakerResult

    def stopRetryingInteraction(interactionName: String): JFuture[String] =
      baker.stopRetryingInteraction(recipeInstanceId, interactionName).toBakerResult

    def resolveInteraction(interactionName: String, eventJson: String): JFuture[String] =
      parseEventAndExecute(eventJson, baker.resolveInteraction(recipeInstanceId, interactionName, _))
  }

  private def toOption[T](opt: Optional[T]): Option[T] = if (opt.isPresent) Some(opt.get()) else None

  private def parseEventAndExecute[A](eventJson: String, f: EventInstance => Future[A])(implicit encoder: Encoder[A]): JFuture[String] =  (for {
    json <- parse(eventJson)
    eventInstance <- json.as[EventInstance]
  } yield {
    f(eventInstance).toBakerResultScalaFuture
  }).getOrElse(Future.failed(new IllegalArgumentException("Can't process event"))).toJava.toCompletableFuture

  private implicit class BakerResultHelperJavaFuture[A](f: => Future[A])(implicit encoder: Encoder[A]) {
    def toBakerResult: JFuture[String] = f.toBakerResultScalaFuture.toJava.toCompletableFuture
  }

  private implicit class BakerResultHelperScalaFuture[A](f: => Future[A])(implicit encoder: Encoder[A]) {
    def toBakerResultScalaFuture(implicit encoder: Encoder[A]): Future[String] = {
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
  }
}
