package com.ing.baker.runtime.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.StatusCodes
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.stream.Materializer
import com.ing.baker.runtime.akka.actor.serialization.{Encryption, SerializersProvider}
import com.ing.baker.runtime.baas.BaaSProto._
import com.ing.baker.runtime.baas.MarshallingUtils._
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Future

object BaaSServer {

  def run(baker: Baker, host: String, port: Int)(implicit system: ActorSystem, mat: Materializer): Future[Http.ServerBinding] = {
    val encryption = Encryption.NoEncryption
    val server = new BaaSServer()(system, mat, baker, encryption)
    Http().bindAndHandle(server.route, host, port)
  }
}

class BaaSServer(implicit system: ActorSystem, mat: Materializer, baker: Baker, encryption: Encryption) {

  import system.dispatcher

  implicit private val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  def route: Route = pathPrefix("api" / "v3")(concat(addRecipe, getRecipe, getAllRecipes, bake,
    fireEventAndResolveWhenReceived, fireEventAndResolveWhenCompleted, fireEventAndResolveOnEvent, fireEvent,
    getAllRecipeInstancesMetadata, getRecipeInstanceState, getVisualState, retryInteraction, resolveInteraction,
    stopRetryingInteraction
  ))

  private def addRecipe: Route = post(path("addRecipe") {
    entity(as[BaaSProtocol.AddRecipeRequest]) { request =>
      complete(baker.addRecipe(request.compiledRecipe).map(BaaSProtocol.AddRecipeResponse))
    }
  })

  private def getRecipe: Route = post(path("getRecipe") {
    entity(as[BaaSProtocol.GetRecipeRequest]) { request =>
      complete(baker.getRecipe(request.recipeId).map(BaaSProtocol.GetRecipeResponse))
    }
  })

  private def getAllRecipes: Route = post(path("getAllRecipes") {
      complete(baker.getAllRecipes.map(BaaSProtocol.GetAllRecipesResponse))
  })

  private def bake: Route = post(path("bake") {
    entity(as[BaaSProtocol.BakeRequest]) { request =>
      onComplete(baker.bake(request.recipeId, request.recipeInstanceId)) { _ =>
        complete(StatusCodes.OK)
      }
    }
  })

  private def fireEventAndResolveWhenReceived: Route = post(path("fireEventAndResolveWhenReceived") {
    entity(as[BaaSProtocol.FireEventAndResolveWhenReceivedRequest]) { request =>
      complete(baker.fireEventAndResolveWhenReceived(request.recipeInstanceId, request.event, request.correlationId)
        .map(BaaSProtocol.FireEventAndResolveWhenReceivedResponse))
    }
  })

  private def fireEventAndResolveWhenCompleted: Route = post(path("fireEventAndResolveWhenCompleted") {
    entity(as[BaaSProtocol.FireEventAndResolveWhenCompletedRequest]) { request =>
      complete(baker.fireEventAndResolveWhenCompleted(request.recipeInstanceId, request.event, request.correlationId)
        .map(BaaSProtocol.FireEventAndResolveWhenCompletedResponse))
    }
  })

  private def fireEventAndResolveOnEvent: Route = post(path("fireEventAndResolveOnEvent") {
    entity(as[BaaSProtocol.FireEventAndResolveOnEventRequest]) { request =>
      complete(baker.fireEventAndResolveOnEvent(request.recipeInstanceId, request.event, request.onEvent, request.correlationId)
        .map(BaaSProtocol.FireEventAndResolveOnEventResponse))
    }
  })

  private def fireEvent: Route = post(path("fireEvent") {
    entity(as[BaaSProtocol.FireEventRequest]) { request =>
      complete(baker.fireEvent(request.recipeInstanceId, request.event, request.correlationId).resolveWhenReceived
        .map(_ => "TODO")) // TODO figure out what to do here with the 2 different futures
    }
  })

  private def getAllRecipeInstancesMetadata: Route = post(path("getAllRecipeInstancesMetadata") {
      complete(baker.getAllRecipeInstancesMetadata
        .map(BaaSProtocol.GetAllRecipeInstancesMetadataResponse))
  })

  private def getRecipeInstanceState: Route = post(path("getRecipeInstanceState") {
    entity(as[BaaSProtocol.GetRecipeInstanceStateRequest]) { request =>
      complete(baker.getRecipeInstanceState(request.recipeInstanceId)
        .map(BaaSProtocol.GetRecipeInstanceStateResponse))
    }
  })

  private def getVisualState: Route = post(path("getVisualState") {
    entity(as[BaaSProtocol.GetVisualStateRequest]) { request =>
      complete(baker.getVisualState(request.recipeInstanceId)
        .map(BaaSProtocol.GetVisualStateResponse))
    }
  })

  private def retryInteraction: Route = post(path("retryInteraction") {
    entity(as[BaaSProtocol.RetryInteractionRequest]) { request =>
      onComplete(baker.retryInteraction(request.recipeInstanceId, request.interactionName)) { _ =>
        complete(StatusCodes.OK)
      }
    }
  })

  private def resolveInteraction: Route = post(path("resolveInteraction") {
    entity(as[BaaSProtocol.ResolveInteractionRequest]) { request =>
      onComplete(baker.resolveInteraction(request.recipeInstanceId, request.interactionName, request.event)) { _ =>
        complete(StatusCodes.OK)
      }
    }
  })

  private def stopRetryingInteraction: Route = post(path("stopRetryingInteraction") {
    entity(as[BaaSProtocol.StopRetryingInteractionRequest]) { request =>
      onComplete(baker.stopRetryingInteraction(request.recipeInstanceId, request.interactionName)) { _ =>
        complete(StatusCodes.OK)
      }
    }
  })

}
