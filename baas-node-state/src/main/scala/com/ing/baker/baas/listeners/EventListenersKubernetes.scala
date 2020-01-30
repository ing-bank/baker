package com.ing.baker.baas.listeners

import akka.actor.ActorSystem
import akka.stream.Materializer
import com.ing.baker.baas.akka.RemoteEventListenerClient
import com.ing.baker.baas.state.KubernetesFunctions
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.Future
import scala.concurrent.duration._

// TODO make this more efficient and thread safe
class EventListenersKubernetes()(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends LazyLogging {

  import system.dispatcher

  type RecipeName = String

  private var listenersCache: Map[RecipeName, List[RemoteEventListenerClient]] = Map.empty

  def loadListeners: Map[RecipeName, List[RemoteEventListenerClient]] = {
    KubernetesFunctions
      .getEventListenersAddresses()
      .map { case (recipe, address) => (recipe, RemoteEventListenerClient(address)) }
      .toList
      .foldLeft(Map.empty[RecipeName, List[RemoteEventListenerClient]]) { case (acc, (recipeName, client)) =>
        acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty[RemoteEventListenerClient])))
      }
  }

  def updateInteractions: Runnable = () => {
    logger.info("Updating the InteractionManager")
    listenersCache = loadListeners
  }

  system.scheduler.schedule(30.seconds, 10.seconds, updateInteractions)

  def registerEventListenerForRemote(recipeName: String, baker: Baker): Future[Unit] = {
    println(Console.YELLOW + s"Event listener for: $recipeName" + Console.RESET)
    baker.registerEventListener(recipeName, (metadata, event) => {
      listenersCache.get(recipeName).foreach(_.foreach(_.apply(metadata, event)))
    })
  }

  def initializeEventListeners(baker: Baker): Future[Unit] =
    for {
      recipes <- baker.getAllRecipes
      _ <- Future.traverse(recipes.toList) { case (_, recipe) => registerEventListenerForRemote(recipe.compiledRecipe.name, baker) }
    } yield ()
}
