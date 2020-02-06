package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.Materializer
import com.ing.baker.baas.akka.RemoteEventListenerClient
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.Future
import scala.concurrent.duration._

// TODO make this more efficient and thread safe (making it an actor is fine)
class EventListenersServiceDiscovery(discovery: ServiceDiscovery, baker: Baker)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends LazyLogging {

  import system.dispatcher

  type RecipeName = String

  private var listenersCache: Map[RecipeName, List[RemoteEventListenerClient]] = Map.empty

  private def loadListeners: Future[Map[RecipeName, List[RemoteEventListenerClient]]] = {
    discovery
      .getEventListenersAddresses
      .map( _
        .map { case (recipe, address) => (recipe, RemoteEventListenerClient(address)) }
        .toList
        .foldLeft(Map.empty[RecipeName, List[RemoteEventListenerClient]]) { case (acc, (recipeName, client)) =>
          acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty[RemoteEventListenerClient])))
        })
  }

  private def updateCache: Runnable = () => {
    loadListeners.foreach { listeners =>
      logger.info("Updating the InteractionManager")
      listenersCache = listeners
    }
  }

  system.scheduler.schedule(30.seconds, 10.seconds, updateCache)

  def initializeEventListeners: Future[Unit] =
    baker.registerEventListener((metadata, event) => {
      listenersCache.get(metadata.recipeName).foreach(_.foreach(_.apply(metadata, event)))
      listenersCache.get("All-Recipes").foreach(_.foreach(_.apply(metadata, event)))
    })
}
