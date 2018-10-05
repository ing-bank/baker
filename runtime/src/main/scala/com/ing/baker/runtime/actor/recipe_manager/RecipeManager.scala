package com.ing.baker.runtime.actor.recipe_manager

import akka.actor.{ActorLogging, Props}
import akka.persistence.PersistentActor
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.BakerProtoMessage
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._

import scala.collection.mutable

object RecipeManager {

  def props() = Props(new RecipeManager)

  //Events
  //When a recipe is added
  case class RecipeAdded(recipeId: String, compiledRecipe: CompiledRecipe, timeStamp: Long) extends BakerProtoMessage

}

class RecipeManager extends PersistentActor with ActorLogging {

  val compiledRecipes: mutable.Map[String, (CompiledRecipe, Long)] = mutable.Map[String, (CompiledRecipe, Long)]()

  private def hasCompiledRecipe(compiledRecipe: CompiledRecipe): Option[String] =
    compiledRecipes.collectFirst { case (recipeId, (`compiledRecipe`, _)) =>  recipeId}

  private def addRecipe(recipeId: String, compiledRecipe: CompiledRecipe, timestamp: Long) =
    compiledRecipes += (recipeId -> (compiledRecipe, timestamp))


  override def receiveCommand: Receive = {
    case AddRecipe(compiledRecipe) =>
      val foundRecipe = hasCompiledRecipe(compiledRecipe)
      if (foundRecipe.isEmpty) {
        val timestamp = System.currentTimeMillis()
        persist(RecipeAdded(compiledRecipe.recipeId, compiledRecipe, timestamp)) { _ =>
          addRecipe(compiledRecipe.recipeId, compiledRecipe, timestamp)
          context.system.eventStream.publish(
            com.ing.baker.runtime.core.events.RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe))
          sender() ! AddRecipeResponse(compiledRecipe.recipeId)
        }
      }
      else {
        sender() ! AddRecipeResponse(foundRecipe.get)
      }

    case GetRecipe(recipeId: String) =>
      compiledRecipes.get(recipeId) match {
        case Some((compiledRecipe, timestamp)) => sender() ! RecipeFound(compiledRecipe, timestamp)
        case None => sender() ! NoRecipeFound(recipeId)
      }

    case GetAllRecipes =>
      sender() ! AllRecipes(compiledRecipes.map {
        case (recipeId, (compiledRecipe, timestamp)) => RecipeInformation(recipeId, compiledRecipe, timestamp)
      }.toSeq)
  }

  override def receiveRecover: Receive = {
    case RecipeAdded(recipeId, compiledRecipe, timeStamp) => addRecipe(recipeId, compiledRecipe, timeStamp)
  }

  override def persistenceId: String = self.path.name
}
