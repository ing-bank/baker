package com.ing.baker.runtime.akka.actor.recipe_manager

import akka.actor.{ActorLogging, Props}
import akka.persistence.PersistentActor
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.logging.LogAndSendEvent
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerActor._
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable

import scala.collection.mutable

object RecipeManagerActor {

  def props() = Props(new RecipeManagerActor)

  //Events
  //When a recipe is added
  case class RecipeAdded(compiledRecipe: CompiledRecipe, timeStamp: Long) extends BakerSerializable
}

class RecipeManagerActor extends PersistentActor with ActorLogging {

  val compiledRecipes: mutable.Map[String, (CompiledRecipe, Long)] = mutable.Map[String, (CompiledRecipe, Long)]()

  private def hasCompiledRecipe(compiledRecipe: CompiledRecipe): Option[String] =
    compiledRecipes.collectFirst { case (recipeId, (`compiledRecipe`, _)) =>  recipeId}

  private def addRecipe(compiledRecipe: CompiledRecipe, timestamp: Long) =
    compiledRecipes += (compiledRecipe.recipeId -> (compiledRecipe, timestamp))


  override def receiveCommand: Receive = {
    case AddRecipe(compiledRecipe) =>
      val foundRecipe = hasCompiledRecipe(compiledRecipe)
      if (foundRecipe.isEmpty) {
        val timestamp = System.currentTimeMillis()
        persist(RecipeAdded(compiledRecipe, timestamp)) { _ =>
          addRecipe(compiledRecipe, timestamp)
          LogAndSendEvent.recipeAdded(com.ing.baker.runtime.scaladsl.RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe), context.system.eventStream)
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
        case (recipeId, (compiledRecipe, timestamp)) => RecipeInformation(compiledRecipe, timestamp)
      }.toSeq)
  }

  override def receiveRecover: Receive = {
    case RecipeAdded(compiledRecipe, timeStamp) => addRecipe(compiledRecipe, timeStamp)
  }

  override def persistenceId: String = self.path.name
}
