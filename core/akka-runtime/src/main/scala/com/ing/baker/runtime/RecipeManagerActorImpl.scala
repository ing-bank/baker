package com.ing.baker.runtime

import _root_.akka.actor.ActorRef
import _root_.akka.pattern._
import _root_.akka.util.Timeout
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._

import scala.concurrent.{ExecutionContext, Future}

class RecipeManagerActorImpl(actor: ActorRef, settings: RecipeManagerActorImpl.Settings)
                            (implicit ec: ExecutionContext) extends RecipeManager {
  override def put(compiledRecipe: CompiledRecipe): Future[String] = {
    implicit val timeout: Timeout = settings.addRecipeTimeout
    (actor ? AddRecipe(compiledRecipe)).mapTo[AddRecipeResponse].map(_.recipeId)
  }

  override def get(recipeId: String): Future[Option[(CompiledRecipe, Long)]] = {
    implicit val timeout: Timeout = settings.inquireTimeout
    (actor ? GetRecipe(recipeId)).map {
      case RecipeFound(compiledRecipe, timestamp) => Some((compiledRecipe, timestamp))
      case NoRecipeFound(_) => None
    }
  }

  override def all: Future[Seq[(CompiledRecipe, Long)]] = {
    implicit val timeout: Timeout = settings.inquireTimeout
    (actor ? GetAllRecipes).mapTo[AllRecipes].map(_.recipes.map { r => (r.compiledRecipe, r.timestamp) })
  }
}

object RecipeManagerActorImpl {
  case class Settings(addRecipeTimeout: Timeout, inquireTimeout: Timeout)
}