package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.bakerlistener.RemoteBakerEventListenerClient
import com.ing.baker.baas.recipelistener.RemoteEventListenerClient
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri

import scala.concurrent.Future
import scala.concurrent.duration._

// TODO make this more efficient and thread safe (making it an actor is fine)
class EventListenersServiceDiscovery(discovery: ServiceDiscovery, baker: Baker)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends LazyLogging {

  import system.dispatcher

  type RecipeName = String

  type RecipeListener = Resource[IO, RemoteEventListenerClient]

  type BakerListener = Resource[IO, RemoteBakerEventListenerClient]

  implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)

  implicit val timer: Timer[IO] = IO.timer(system.dispatcher)

  private var recipeListenersCache: Map[RecipeName, List[RecipeListener]] = Map.empty

  private var bakerListenersCache: List[BakerListener] = List.empty

  private def loadListeners: Future[Map[RecipeName, List[RecipeListener]]] = {
    discovery
      .getEventListenersAddresses
      .map(_
        .map { case (recipe, address) => (recipe, RemoteEventListenerClient.resource(Uri.unsafeFromString(address), system.dispatcher)) }
        .toList
        .foldLeft(Map.empty[RecipeName, List[RecipeListener]]) { case (acc, (recipeName, client)) =>
          acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty[RecipeListener])))
        })
  }

  private def loadBakerListeners: Future[List[BakerListener]] = {
    discovery
      .getBakerEventListenersAddresses
      .map(_
        .map( address => RemoteBakerEventListenerClient.resource(Uri.unsafeFromString(address), system.dispatcher))
        .toList)
  }

  private def updateCache: Runnable = () => {
    loadListeners.foreach { listeners =>
      recipeListenersCache = listeners
    }
    loadBakerListeners.foreach { listeners =>
      bakerListenersCache = listeners
    }
  }

  system.scheduler.schedule(0.seconds, 10.seconds, updateCache)

  def initializeEventListeners: Future[Unit] = {
    baker.registerEventListener((metadata, event) => {
      recipeListenersCache.get(metadata.recipeName).foreach(_.foreach(_.use(_.apply(metadata, event)).unsafeRunAsyncAndForget()))
      recipeListenersCache.get("All-Recipes").foreach(_.foreach(_.use(_.apply(metadata, event)).unsafeRunAsyncAndForget()))
    })
    baker.registerBakerEventListener(event => {
      bakerListenersCache.foreach(_.use(_.apply(event)).unsafeRunAsyncAndForget())
    })
  }
}
