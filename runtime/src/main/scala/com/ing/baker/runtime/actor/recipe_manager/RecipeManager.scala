package com.ing.baker.runtime.actor.recipe_manager

import akka.actor.{ActorLogging, Props}
import akka.persistence.PersistentActor
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.InternalBakerEvent
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._

import scala.collection.mutable

object RecipeManager {

  def props() = Props(new RecipeManager)

  //Events
  //When a recipe is added
  case class RecipeAdded(recipeId: String, compiledRecipe: CompiledRecipe) extends InternalBakerEvent
}

class RecipeManager extends PersistentActor with ActorLogging {

  val compiledRecipes: mutable.Map[String, CompiledRecipe] = mutable.Map[String, CompiledRecipe]()

  private def hasCompiledRecipe(compiledRecipe: CompiledRecipe): Option[String] =
    compiledRecipes.find(_._2 == compiledRecipe).map(_._1)

  private def addRecipe(recipeId: String, compiledRecipe: CompiledRecipe) =
    compiledRecipes += (recipeId -> compiledRecipe)


  override def receiveCommand: Receive = {
    case AddRecipe(compiledRecipe) => {
      val foundRecipe = hasCompiledRecipe(compiledRecipe)
      if(foundRecipe.isEmpty) {

        persist(RecipeAdded(compiledRecipe.recipeId, compiledRecipe)){ _ =>
          addRecipe(compiledRecipe.recipeId, compiledRecipe)
          context.system.eventStream.publish(
            com.ing.baker.runtime.core.events.RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, System.currentTimeMillis(), compiledRecipe))
          sender() ! RecipeSuccessfullyAdded
        }
      }
      else{
        sender() ! RecipeSuccessfullyAdded
      }
    }
    case GetRecipe(recipeId: String) => {
      compiledRecipes.get(recipeId) match {
        case Some(compiledRecipe) => sender() ! RecipeFound(compiledRecipe)
        case None => sender() ! NoRecipeFound(recipeId)
      }
    }
    case GetAllRecipes => {
      sender() ! AllRecipes(compiledRecipes.toMap)
    }
  }

  override def receiveRecover: Receive = {
    case RecipeAdded(recipeId, compiledRecipe) =>
      // old recipes (before 1.4.0) do not have a recipe id, so we need to copy it from the event
      addRecipe(recipeId, compiledRecipe.copy(recipeId = recipeId))
  }

  override def persistenceId: String = self.path.name
}
