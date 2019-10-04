package com.ing.baker.runtime.baas.scaladsl

import java.util.Optional

import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec
import com.ing.baker.runtime.baas.javadsl
import com.ing.baker.runtime.baas.scaladsl.JavaDSLBaaSServerClientSpec.optionToJava
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.types.Value

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.Future

class JavaDSLBaaSServerClientSpec extends CommonBaaSServerClientSpec(
  (host, as, mat) => {
    import as.dispatcher
    val javaBaker = javadsl.Baker.remote(host, as, mat)
    new scaladsl.Baker {
      override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] =
        FutureConverters.toScala(javaBaker.addRecipe(compiledRecipe))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getRecipe(recipeId: String): Future[RecipeInformation] =
        FutureConverters.toScala(javaBaker.getRecipe(recipeId)).map(_.asScala)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getAllRecipes: Future[Map[String, RecipeInformation]] =
        FutureConverters.toScala(javaBaker.getAllRecipes).map(_.asScala.mapValues(_.asScala).toMap)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
        FutureConverters.toScala(javaBaker.bake(recipeId, recipeInstanceId))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] =
        FutureConverters.toScala(javaBaker.fireEventAndResolveWhenReceived(recipeInstanceId, event.asJava, optionToJava(correlationId)))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventResult] =
        FutureConverters.toScala(javaBaker.fireEventAndResolveWhenCompleted(recipeInstanceId, event.asJava, optionToJava(correlationId))).map(_.asScala)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): Future[SensoryEventResult] =
        FutureConverters.toScala(javaBaker.fireEventAndResolveOnEvent(recipeInstanceId, event.asJava, onEvent, optionToJava(correlationId))).map(_.asScala)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = {
        val res = javaBaker.fireEvent(recipeInstanceId, event.asJava, optionToJava(correlationId))
        scaladsl.EventResolutions(
          FutureConverters.toScala(res.resolveWhenReceived)
            .recoverWith {
              case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
            },
          FutureConverters.toScala(res.resolveWhenCompleted).map(_.asScala)
            .recoverWith {
              case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
            }
        )
      }
      override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] =
        FutureConverters.toScala(javaBaker.getAllRecipeInstancesMetadata).map(_.asScala.toSet.map((x: com.ing.baker.runtime.javadsl.RecipeInstanceMetadata) => x.asScala))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
        FutureConverters.toScala(javaBaker.getRecipeInstanceState(recipeInstanceId)).map(_.asScala)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
        FutureConverters.toScala(javaBaker.getIngredients(recipeInstanceId)).map(_.asScala.toMap)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
        FutureConverters.toScala(javaBaker.getEvents(recipeInstanceId)).map(_.asScala.map(_.asScala))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getEventNames(recipeInstanceId: String): Future[Seq[String]] =
        FutureConverters.toScala(javaBaker.getEventNames(recipeInstanceId)).map(_.asScala)
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): Future[String] =
        FutureConverters.toScala(javaBaker.getVisualState(recipeInstanceId, style))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def registerEventListener(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
        ???
      override def registerEventListener(listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
        ???
      override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] =
        ???
      override def addInteractionInstance(implementation: InteractionInstance): Future[Unit] =
        ???
      override def addInteractionInstances(implementations: Seq[InteractionInstance]): Future[Unit] =
        ???
      override def gracefulShutdown(): Future[Unit] =
        FutureConverters.toScala(javaBaker.gracefulShutdown())
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
        FutureConverters.toScala(javaBaker.retryInteraction(recipeInstanceId, interactionName))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
        FutureConverters.toScala(javaBaker.resolveInteraction(recipeInstanceId, interactionName, event.asJava))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
      override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
        FutureConverters.toScala(javaBaker.stopRetryingInteraction(recipeInstanceId, interactionName))
          .recoverWith {
            case e: java.util.concurrent.CompletionException => Future.failed(e.getCause)
          }
    }
  }
)

object JavaDSLBaaSServerClientSpec {

  def optionToJava[A](option: Option[A]): Optional[A] =
    option match {
      case Some(a) => Optional.of(a)
      case None => Optional.empty()
    }
}