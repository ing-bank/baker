package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.Materializer
import com.ing.baker.baas.akka.{RemoteBakerEventListenerClient, RemoteEventListenerClient}
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.Future
import scala.concurrent.duration._

// TODO make this more efficient and thread safe (making it an actor is fine)
class EventListenersServiceDiscovery(discovery: ServiceDiscovery, baker: Baker)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends LazyLogging {

  import system.dispatcher

  type RecipeName = String

  private var recipeListenersCache: Map[RecipeName, List[RemoteEventListenerClient]] = Map.empty
  private var bakerListenersCache: List[RemoteBakerEventListenerClient] = List.empty

  private def loadListeners: Future[Map[RecipeName, List[RemoteEventListenerClient]]] = {
    discovery
      .getEventListenersAddresses
      .map(_
        .map { case (recipe, address) => (recipe, RemoteEventListenerClient(address)) }
        .toList
        .foldLeft(Map.empty[RecipeName, List[RemoteEventListenerClient]]) { case (acc, (recipeName, client)) =>
          acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty[RemoteEventListenerClient])))
        })
  }

  private def loadBakerListeners: Future[List[RemoteBakerEventListenerClient]] = {
    discovery
      .getBakerEventListenersAddresses
      .map(_
        .map(RemoteBakerEventListenerClient(_))
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
      recipeListenersCache.get(metadata.recipeName).foreach(_.foreach(_.apply(metadata, event)))
      recipeListenersCache.get("All-Recipes").foreach(_.foreach(_.apply(metadata, event)))
    })
    baker.registerBakerEventListener(event => {
      bakerListenersCache.foreach(_.apply(event))
    })
  }
}
