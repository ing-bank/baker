package com.ing.baker.runtime.actor.recipemanager

import java.util.UUID

import akka.actor.{ActorLogging, Props}
import akka.persistence.PersistentActor
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.recipemanager.RecipeManager._
import com.ing.baker.runtime.actor.{InternalBakerEvent, InternalBakerMessage}

import scala.collection.mutable

object RecipeManager {

  def props() = Props(new RecipeManager)

  //Add a recipe
  case class AddRecipe(compiledRecipe: CompiledRecipe) extends InternalBakerMessage

  case class AddRecipeResponse(recipeId: String) extends InternalBakerMessage

  //Get a specific recipe
  case class GetRecipe(recipeId: String) extends InternalBakerMessage

  case class RecipeFound(compiledRecipe: CompiledRecipe) extends InternalBakerMessage

  case object NoRecipeFound extends InternalBakerMessage

  //Get alla recipe
  case object GetAllRecipes extends InternalBakerMessage

  case class AllRecipes(compiledRecipes: Map[String, CompiledRecipe]) extends InternalBakerMessage

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
        val recipeId = UUID.randomUUID().toString

        persist(RecipeAdded(recipeId, compiledRecipe)){ _ =>
          addRecipe(recipeId, compiledRecipe)
          sender() ! AddRecipeResponse(recipeId)
        }
      }
      else{
        sender() ! AddRecipeResponse(foundRecipe.get)
      }
    }
    case GetRecipe(recipeId: String) => {
      compiledRecipes.get(recipeId) match {
        case Some(compiledRecipe) => sender() ! RecipeFound(compiledRecipe)
        case None => sender() ! NoRecipeFound
      }
    }
    case GetAllRecipes => {
      sender() ! AllRecipes(compiledRecipes.toMap)
    }
  }

  override def receiveRecover: Receive = {
    case RecipeAdded(recipeId, compiledRecipe) => addRecipe(recipeId, compiledRecipe)
  }

  override def persistenceId: String = self.path.name
}
