package com.ing.baker.runtime

import _root_.akka.actor.ActorRef
import _root_.akka.pattern._
import _root_.akka.util.Timeout
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.common.RecipeRecord

import scala.concurrent.{ExecutionContext, Future}

private class RecipeManagerActorImpl(actor: ActorRef, settings: RecipeManagerActorImpl.Settings)
                            (implicit val ex: ExecutionContext) extends RecipeManager {

  override def put(recipeRecord: RecipeRecord): Future[String] = {
    implicit val timeout: Timeout = settings.addRecipeTimeout
    (actor ? AddRecipe(recipeRecord.recipe)).mapTo[AddRecipeResponse].map(_.recipeId)
  }

  override def get(recipeId: String): Future[Option[RecipeRecord]] = {
    implicit val timeout: Timeout = settings.inquireTimeout
    (actor ? GetRecipe(recipeId)).map {
      case RecipeFound(compiledRecipe, timestamp) => Some(RecipeRecord.of(compiledRecipe, updated = timestamp))
      case NoRecipeFound(_) => None
    }
  }

  override def all: Future[Seq[RecipeRecord]] = {
        implicit val timeout: Timeout = settings.inquireTimeout
        (actor ? GetAllRecipes).mapTo[AllRecipes].map(_.recipes.map { r => RecipeRecord.of(r.compiledRecipe, updated = r.timestamp) })
  }
}

object RecipeManagerActorImpl {
  case class Settings(addRecipeTimeout: Timeout, inquireTimeout: Timeout)

  def pollingAware(actor: ActorRef, settings: RecipeManagerActorImpl.Settings)
           (implicit ex: ExecutionContext): RecipeManager = new RecipeManagerActorImpl(actor, settings) with PollingAware
}
