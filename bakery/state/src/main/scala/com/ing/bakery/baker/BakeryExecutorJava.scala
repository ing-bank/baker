package com.ing.bakery.baker

import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{BakerResult, EncodedRecipe, EventInstance}
import com.ing.baker.runtime.serialization.JsonDecoders._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.typesafe.scalalogging.LazyLogging
import io.circe.Encoder
import io.circe.generic.auto._
import io.circe.parser.parse

import java.nio.charset.Charset
import java.util.Optional
import java.util.concurrent.{CompletableFuture => JFuture}
import scala.compat.java8.FutureConverters.FutureOps
import scala.concurrent.{ExecutionContext, Future}

class BakeryExecutorJava(bakery: Bakery) extends LazyLogging {

  implicit val executionContext: ExecutionContext = bakery.executionContext

  private def callBaker[A](f: => Future[A])(implicit encoder: Encoder[A]): Future[String] = {
    f.map {
      case () => BakerResult.Ack
      case a => BakerResult(a)
    }.recover {
      case e: BakerException => BakerResult(e)
      case e: Throwable =>
        logger.error(s"Unexpected exception happened when calling Baker", e)
        BakerResult(e.getMessage)
    }.map(bakerResultEncoder.apply(_).noSpaces)
  }

  private def callBakerJava[A](f: => Future[A])(implicit encoder: Encoder[A]): JFuture[String] = {
    callBaker(f)(encoder).toJava.toCompletableFuture
  }

  def appGetAllInteractions: JFuture[String] = callBakerJava(bakery.baker.getAllInteractions)

  def appGetInteraction(interactionName: String): JFuture[String] = callBakerJava(bakery.baker.getInteraction(interactionName))

  def appAddRecipe(recipe: String): JFuture[String] = {
    (for {
      json <- parse(recipe).toOption
      encodedRecipe <- json.as[EncodedRecipe].toOption
    } yield RecipeLoader.fromBytes(encodedRecipe.base64.getBytes(Charset.forName("UTF-8"))).unsafeToFuture())
      .map(_.flatMap(recipe => callBaker(bakery.baker.addRecipe(recipe, validate = false))))
      .getOrElse(Future.failed(new IllegalStateException("Error adding recipe")))
  }.toJava.toCompletableFuture

  def appGetRecipe(recipeId: String): JFuture[String] = callBakerJava(bakery.baker.getRecipe(recipeId))

  def appGetAllRecipes: JFuture[String] = callBakerJava(bakery.baker.getAllRecipes)

  def appGetVisualRecipe(recipeId: String): JFuture[String] = callBakerJava(bakery.baker.getRecipeVisual(recipeId))

  def instanceGet(recipeInstanceId: String): JFuture[String] =  callBakerJava(bakery.baker.getRecipeInstanceState(recipeInstanceId))

  def instanceGetEvents(recipeInstanceId: String): JFuture[String] = callBakerJava(bakery.baker.getEvents(recipeInstanceId))

  def instanceGetIngredients(recipeInstanceId: String): JFuture[String] = callBakerJava(bakery.baker.getIngredients(recipeInstanceId))

  def instanceGetVisual(recipeInstanceId: String): JFuture[String] = callBakerJava(bakery.baker.getVisualState(recipeInstanceId))

  def instanceBake(recipeId: String, recipeInstanceId: String): JFuture[String] = callBakerJava(bakery.baker.bake(recipeId, recipeInstanceId))

  private def toOption[T](opt: Optional[T]): Option[T] = if (opt.isPresent) Some(opt.get()) else None

  private def parseEventAndExecute[A](eventJson: String, f: EventInstance => Future[A])(implicit encoder: Encoder[A]): JFuture[String] =  (for {
    json <- parse(eventJson)
    eventInstance <- json.as[EventInstance]
  } yield {
    callBaker(f(eventInstance))
  }).getOrElse(Future.failed(new IllegalArgumentException("Can't process event"))).toJava.toCompletableFuture

  def instanceFireAndResolveWhenReceived(recipeInstanceId: String, eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveWhenReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

  def instanceFireAndResolveWhenCompleted(recipeInstanceId: String, eventJson: String, maybeCorrelationId: Optional[String]): JFuture[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveWhenCompleted(recipeInstanceId, _, toOption(maybeCorrelationId)))

  def instancefireAndResolveOnEvent(recipeInstanceId: String, eventJson: String, event: String, maybeCorrelationId: Optional[String]): JFuture[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveOnEvent(recipeInstanceId, _, event, toOption(maybeCorrelationId)))

  def instanceInteractionRetry(recipeInstanceId: String, interactionName: String): JFuture[String] =
    callBakerJava(bakery.baker.retryInteraction(recipeInstanceId, interactionName))

  def instanceInteractionStopRetrying(recipeInstanceId: String, interactionName: String): JFuture[String] =
    callBakerJava(bakery.baker.stopRetryingInteraction(recipeInstanceId, interactionName))

  def instanceInteractionResolve(recipeInstanceId: String, interactionName: String, eventJson: String): JFuture[String] =
    parseEventAndExecute(eventJson, bakery.baker.resolveInteraction(recipeInstanceId, interactionName, _))

}
