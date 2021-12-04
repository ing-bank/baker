package com.ing.bakery.baker

import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{BakerResult, EncodedRecipe, EventInstance}
import com.typesafe.scalalogging.LazyLogging
import io.circe.Encoder
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.JsonDecoders._
import io.circe.parser.parse
import io.circe._
import io.circe.generic.auto._

import java.nio.charset.Charset
import java.util.Optional
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

  def appGetAllInteractions: Future[String] = callBaker(bakery.baker.getAllInteractions)

  def appGetInteraction(interactionName: String): Future[String] = callBaker(bakery.baker.getInteraction(interactionName))

  def appAddRecipe(recipe: String): Future[String] = {
    (for {
      json <- parse(recipe).toOption
      encodedRecipe <- json.as[EncodedRecipe].toOption
    } yield RecipeLoader.fromBytes(encodedRecipe.base64.getBytes(Charset.forName("UTF-8"))).unsafeToFuture)
      .map(_.flatMap(recipe => callBaker(bakery.baker.addRecipe(recipe, validate = false))))
      .getOrElse(Future.failed(new IllegalStateException("Error adding recipe")))
  }

  def appGetRecipe(recipeId: String): Future[String] = callBaker(bakery.baker.getRecipe(recipeId))

  def appGetAllRecipes: Future[String] = callBaker(bakery.baker.getAllRecipes)

  def appGetVisualRecipe(recipeId: String): Future[String] = callBaker(bakery.baker.getRecipeVisual(recipeId))

  def instanceGet(recipeInstanceId: String): Future[String] =  callBaker(bakery.baker.getRecipeInstanceState(recipeInstanceId))

  def instanceGetEvents(recipeInstanceId: String): Future[String] = callBaker(bakery.baker.getEvents(recipeInstanceId))

  def instanceGetIngredients(recipeInstanceId: String): Future[String] = callBaker(bakery.baker.getIngredients(recipeInstanceId))

  def instanceGetVisual(recipeInstanceId: String): Future[String] = callBaker(bakery.baker.getVisualState(recipeInstanceId))

  def instanceBake(recipeInstanceId: String): Future[String] = callBaker(bakery.baker.getVisualState(recipeInstanceId))

  private def toOption[T](opt: Optional[T]): Option[T] = if (opt.isPresent) Some(opt.get()) else None

  private def parseEventAndExecute[A](eventJson: String, f: EventInstance => Future[A])(implicit encoder: Encoder[A]) =  (for {
    json <- parse(eventJson)
    eventInstance <- json.as[EventInstance]
  } yield {
    callBaker(f(eventInstance))
  }).getOrElse(Future.failed(new IllegalArgumentException("Can't process event")))

  def instanceFireAndResolveWhenReceived(recipeInstanceId: String, eventJson: String, maybeCorrelationId: Optional[String]): Future[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveWhenReceived(recipeInstanceId, _, toOption(maybeCorrelationId)))

  def instanceFireAndResolveWhenCompleted(recipeInstanceId: String, eventJson: String, maybeCorrelationId: Optional[String]): Future[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveWhenCompleted(recipeInstanceId, _, toOption(maybeCorrelationId)))

  def instancefireAndResolveOnEvent(recipeInstanceId: String, eventJson: String, event: String, maybeCorrelationId: Optional[String]): Future[String] =
    parseEventAndExecute(eventJson, bakery.baker.fireEventAndResolveOnEvent(recipeInstanceId, _, event, toOption(maybeCorrelationId)))

  def instanceInteractionRetry(recipeInstanceId: String, interactionName: String): Future[String] =
    callBaker(bakery.baker.retryInteraction(recipeInstanceId, interactionName))

  def instanceInteractionStopRetrying(recipeInstanceId: String, interactionName: String): Future[String] =
    callBaker(bakery.baker.stopRetryingInteraction(recipeInstanceId, interactionName))

  def instanceInteractionResolve(recipeInstanceId: String, interactionName: String, eventJson: String): Future[String] =
    parseEventAndExecute(eventJson, bakery.baker.resolveInteraction(recipeInstanceId, interactionName, _))

}
