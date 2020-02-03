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


/** TODO 1 make this more efficient and thread safe (making it an actor is fine)
  * TODO 2 as it is right now, registering remote event listeners does not happen on all nodes when:
  *   1 - cluster inits and node1 and node2 call initializeEventListeners with 0 returned recipes
  *   2 - client adds recipe on node1 and node1 calls registerEventListenerForRemote, the recipe is
  *       in the RecipeManager but node2 never calls registerEventListenerForRemote for such recipe
  *   3 - if a process of the recipe is baked on node2, the remote event listener is never called
  *   POSSIBLE SOLUTION: Make a RecipeManager callback or event listener when a node adds a recipe,
  *                      so to call registerEventListenerForRemote on each added recipe
  *
  */
class EventListenersKubernetes(kube: KubernetesFunctions, baker: Baker)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends LazyLogging {

  import system.dispatcher

  type RecipeName = String

  private var listenersCache: Map[RecipeName, List[RemoteEventListenerClient]] = Map.empty

  def loadListeners: Map[RecipeName, List[RemoteEventListenerClient]] = {
    kube
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

  def registerEventListenerForRemote(recipeName: String): Future[Unit] = {
    baker.registerEventListener(recipeName, (metadata, event) => {
      listenersCache.get(recipeName).foreach(_.foreach(_.apply(metadata, event)))
      listenersCache.get("All-Recipes").foreach(_.foreach(_.apply(metadata, event)))
    })
  }

  def initializeEventListeners: Future[Unit] =
    for {
      recipes <- baker.getAllRecipes
      _ <- Future.traverse(recipes.toList) { case (_, recipe) => registerEventListenerForRemote(recipe.compiledRecipe.name) }
    } yield ()
}
