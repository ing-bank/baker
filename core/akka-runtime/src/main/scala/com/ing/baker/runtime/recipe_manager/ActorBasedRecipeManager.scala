package com.ing.baker.runtime.recipe_manager

import _root_.akka.actor.{ActorRef, ActorSystem, PoisonPill}
import _root_.akka.pattern._
import _root_.akka.util.Timeout
import akka.cluster.Cluster
import akka.cluster.singleton.{ClusterSingletonManager, ClusterSingletonManagerSettings, ClusterSingletonProxy, ClusterSingletonProxySettings}
import com.ing.baker.runtime.akka.AkkaBakerConfig._
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider.recipeManagerName
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerActor
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.common.RecipeRecord
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.{ExecutionContext, Future}

private class ActorBasedRecipeManager(actor: ActorRef, timeouts: Timeouts)(implicit val ex: ExecutionContext) extends RecipeManager {

  override def put(recipeRecord: RecipeRecord): Future[String] = {
    implicit val timeout: Timeout = timeouts.defaultAddRecipeTimeout
    (actor ? AddRecipe(recipeRecord.recipe)).mapTo[AddRecipeResponse].map(_.recipeId)
  }

  override def get(recipeId: String): Future[Option[RecipeRecord]] = {
    implicit val timeout: Timeout = timeouts.defaultInquireTimeout
    (actor ? GetRecipe(recipeId)).map {
      case RecipeFound(compiledRecipe, timestamp) => Some(RecipeRecord.of(compiledRecipe, updated = timestamp))
      case NoRecipeFound(_) => None
    }
  }

  override def all: Future[Seq[RecipeRecord]] = {
        implicit val timeout: Timeout = timeouts.defaultInquireTimeout
        (actor ? GetAllRecipes).mapTo[AllRecipes].map(_.recipes.map { r => RecipeRecord.of(r.compiledRecipe, updated = r.timestamp) })
  }
}

object ActorBasedRecipeManager {
  def pollingAware(actor: ActorRef, timeouts: Timeouts)
           (implicit ex: ExecutionContext): RecipeManager = new ActorBasedRecipeManager(actor, timeouts) with PollingAware

  def clusterBasedRecipeManagerActor(implicit actorSystem: ActorSystem, timeouts: Timeouts): RecipeManager = {
    val singletonManagerProps = ClusterSingletonManager.props(
      RecipeManagerActor.props(),
      terminationMessage = PoisonPill,
      settings = ClusterSingletonManagerSettings(actorSystem))
    val roles = Cluster(actorSystem).selfRoles

    actorSystem.actorOf(props = singletonManagerProps, name = recipeManagerName)

    val singletonProxyProps = ClusterSingletonProxy.props(
      singletonManagerPath = s"/user/$recipeManagerName",
      settings = {
        if (roles.contains("state-node"))
          ClusterSingletonProxySettings(actorSystem).withRole("state-node")
        else
          ClusterSingletonProxySettings(actorSystem)
      })
    import actorSystem.dispatcher
    pollingAware(
      actor = actorSystem.actorOf(props = singletonProxyProps, name = "RecipeManagerProxy"),
      timeouts = timeouts
    )
  }

  def localBasedRecipeManagerActor(actorSystem: ActorSystem, timeouts: Timeouts): RecipeManager = {
    pollingAware(
      actor = actorSystem.actorOf(RecipeManagerActor.props()),
      timeouts = timeouts)(actorSystem.dispatcher)
  }

  def getRecipeManagerActor(actorSystem: ActorSystem, config: Config): RecipeManager = {
    config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local") => localBasedRecipeManagerActor(actorSystem, Timeouts.apply(config))
      case Some("cluster-sharded") =>clusterBasedRecipeManagerActor(actorSystem, Timeouts.apply(config))
      case Some(other) => throw new IllegalArgumentException(s"Unsupported actor provider configured: $other")
    }
  }
}
