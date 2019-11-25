package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.cluster.pubsub.{DistributedPubSub, DistributedPubSubMediator}
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.StatusCodes
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.stream.Materializer
import com.ing.baker.baas.protocol.{BaaSProtocol, ProtocolDistributedEventPublishing}
import com.ing.baker.baas.protocol.BaaSProto._
import com.ing.baker.baas.protocol.MarshallingUtils._
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.{Encryption, SerializersProvider}

import scala.concurrent.{ExecutionContext, Future}

object BaaSServer {

  def run(baker: Baker, host: String, port: Int)(implicit system: ActorSystem, mat: Materializer): Future[Http.ServerBinding] = {
    import system.dispatcher
    val encryption = Encryption.NoEncryption
    val server = new BaaSServer()(system, mat, baker, encryption)
    for {
      _ <- initializeEventListeners(baker, system)
      binding <- Http().bindAndHandle(server.route, host, port)
    } yield binding
  }

  private[state] def registerEventListenerForRemote(recipeName: String, baker: Baker, system: ActorSystem): Future[Unit] = {
    println(Console.YELLOW + s"Event listener for: $recipeName" + Console.RESET)
    baker.registerEventListener(recipeName, (metadata, event) => {
      val eventsTopic: String =
        ProtocolDistributedEventPublishing.eventsTopic(recipeName)
      DistributedPubSub(system).mediator ! DistributedPubSubMediator.Publish(eventsTopic, ProtocolDistributedEventPublishing.Event(metadata, event))
    })
  }

  private[state] def initializeEventListeners(baker: Baker, system: ActorSystem)(implicit ec: ExecutionContext): Future[Unit] =
    for {
      recipes <- baker.getAllRecipes
      _ <- Future.traverse(recipes.toList) { case (_, recipe) => registerEventListenerForRemote(recipe.compiledRecipe.name, baker, system) }
    } yield ()
}

class BaaSServer(implicit system: ActorSystem, mat: Materializer, baker: Baker, encryption: Encryption) {

  import system.dispatcher

  implicit private val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  def route: Route = concat(haproxyCheck, pathPrefix("api" / "v3")(concat(health, addRecipe, getRecipe, getAllRecipes, bake,
    fireEventAndResolveWhenReceived, fireEventAndResolveWhenCompleted, fireEventAndResolveOnEvent, fireEvent,
    getAllRecipeInstancesMetadata, getRecipeInstanceState, getVisualState, retryInteraction, resolveInteraction,
    stopRetryingInteraction
  )))

  private def haproxyCheck: Route = pathSingleSlash(get(complete(StatusCodes.OK)))

  private def health: Route = get(complete("Ok"))

  private def addRecipe: Route = post(path("addRecipe") {
    entity(as[BaaSProtocol.AddRecipeRequest]) { request =>
      val result = for {
        recipeId <- baker.addRecipe(request.compiledRecipe)
        _ <- BaaSServer.registerEventListenerForRemote(request.compiledRecipe.name, baker, system)
      } yield BaaSProtocol.AddRecipeResponse(recipeId)
      completeWithBakerFailures(result)
    }
  })

  private def getRecipe: Route = post(path("getRecipe") {
    entity(as[BaaSProtocol.GetRecipeRequest]) { request =>
      completeWithBakerFailures(baker.getRecipe(request.recipeId).map(BaaSProtocol.GetRecipeResponse))
    }
  })

  private def getAllRecipes: Route = post(path("getAllRecipes") {
      completeWithBakerFailures(baker.getAllRecipes.map(BaaSProtocol.GetAllRecipesResponse))
  })

  private def bake: Route = post(path("bake") {
    entity(as[BaaSProtocol.BakeRequest]) { request =>
      completeWithBakerFailures(baker.bake(request.recipeId, request.recipeInstanceId))
    }
  })

  private def fireEventAndResolveWhenReceived: Route = post(path("fireEventAndResolveWhenReceived") {
    entity(as[BaaSProtocol.FireEventAndResolveWhenReceivedRequest]) { request =>
      completeWithBakerFailures(baker.fireEventAndResolveWhenReceived(request.recipeInstanceId, request.event, request.correlationId)
        .map(BaaSProtocol.FireEventAndResolveWhenReceivedResponse))
    }
  })

  private def fireEventAndResolveWhenCompleted: Route = post(path("fireEventAndResolveWhenCompleted") {
    entity(as[BaaSProtocol.FireEventAndResolveWhenCompletedRequest]) { request =>
      completeWithBakerFailures(baker.fireEventAndResolveWhenCompleted(request.recipeInstanceId, request.event, request.correlationId)
        .map(BaaSProtocol.FireEventAndResolveWhenCompletedResponse))
    }
  })

  private def fireEventAndResolveOnEvent: Route = post(path("fireEventAndResolveOnEvent") {
    entity(as[BaaSProtocol.FireEventAndResolveOnEventRequest]) { request =>
      completeWithBakerFailures(baker.fireEventAndResolveOnEvent(request.recipeInstanceId, request.event, request.onEvent, request.correlationId)
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
      completeWithBakerFailures(baker.getAllRecipeInstancesMetadata
        .map(BaaSProtocol.GetAllRecipeInstancesMetadataResponse))
  })

  private def getRecipeInstanceState: Route = post(path("getRecipeInstanceState") {
    entity(as[BaaSProtocol.GetRecipeInstanceStateRequest]) { request =>
      completeWithBakerFailures(baker.getRecipeInstanceState(request.recipeInstanceId)
        .map(BaaSProtocol.GetRecipeInstanceStateResponse))
    }
  })

  private def getVisualState: Route = post(path("getVisualState") {
    entity(as[BaaSProtocol.GetVisualStateRequest]) { request =>
      completeWithBakerFailures(baker.getVisualState(request.recipeInstanceId)
        .map(BaaSProtocol.GetVisualStateResponse))
    }
  })

  private def retryInteraction: Route = post(path("retryInteraction") {
    entity(as[BaaSProtocol.RetryInteractionRequest]) { request =>
      completeWithBakerFailures(baker.retryInteraction(request.recipeInstanceId, request.interactionName))
    }
  })

  private def resolveInteraction: Route = post(path("resolveInteraction") {
    entity(as[BaaSProtocol.ResolveInteractionRequest]) { request =>
      completeWithBakerFailures(baker.resolveInteraction(request.recipeInstanceId, request.interactionName, request.event))
    }
  })

  private def stopRetryingInteraction: Route = post(path("stopRetryingInteraction") {
    entity(as[BaaSProtocol.StopRetryingInteractionRequest]) { request =>
      completeWithBakerFailures(baker.stopRetryingInteraction(request.recipeInstanceId, request.interactionName))
    }
  })

}
