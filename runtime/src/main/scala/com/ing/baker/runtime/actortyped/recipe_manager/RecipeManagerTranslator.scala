package com.ing.baker.runtime.actortyped.recipe_manager

import akka.actor.typed.{ActorRef, Behavior}
import akka.actor.typed.SupervisorStrategy
import akka.actor.typed.scaladsl.Behaviors
import akka.actor.typed.scaladsl.adapter._
import akka.actor.{Actor, Props}
import akka.event.EventStream
import akka.util.Timeout
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManagerProtocol => UntypedProtocol}

import scala.util.{ Failure, Success }

object RecipeManagerTranslator {

/*
  def props(recipeManagerName: String, timeout: Timeout): Props = Props(new RecipeManagerTranslator(recipeManagerName)(timeout))


  def behavior(recipeManagerName: String, eventStream: EventStream): Behavior[Nothing] =
    Behaviors.setup { context =>

      val forwardActor: ActorRef[RecipeManagerTyped.Command] = context.spawn(
        Behaviors
          .supervise(RecipeManagerTyped.behaviour(eventStream))
          .onFailure[Exception](SupervisorStrategy.restart), recipeManagerName)

      Behaviors.receiveMessage {

        case UntypedProtocol.AddRecipe(compiledRecipe) =>
          context.ask(forwardActor)(RecipeManagerTyped.AddRecipe(compiledRecipe)){
            case Success(RecipeManagerTyped.AddRecipeResponse(recipeId)) =>
            case Failure(exception) =>
          }

        case _ =>

        //Get a specific recipe
        case UntypedProtocol.GetRecipe(recipeId: String) =>

        case UntypedProtocol.RecipeFound(compiledRecipe: CompiledRecipe, timestamp: Long) =>

        case UntypedProtocol.NoRecipeFound(recipeId: String) =>

        //Get all recipes
        case GetAllRecipes =>

        case UntypedProtocol.RecipeInformation(compiledRecipe: CompiledRecipe, timestamp: Long)

        case UntypedProtocol.AllRecipes(recipes: Seq[RecipeInformation]) =>
      }

    }

}

class RecipeManagerTranslator(recipeManagerName: String)(implicit timeout: Timeout) extends Actor {

  val forwardActor: ActorRef[RecipeManagerTyped.Command] = context.spawn(
    Behaviors
      .supervise(RecipeManagerTyped.behaviour(context.system.getEventStream))
      .onFailure[Exception](SupervisorStrategy.restart), recipeManagerName)

  override def receive: Receive = {

    case UntypedProtocol.AddRecipe(compiledRecipe) =>
      forwardActor ! RecipeManagerTyped.AddRecipe(compiledRecipe)(self.toTyped)

    case RecipeManagerTyped.AddRecipeResponse(recipeId) =>

    //Get a specific recipe
    case UntypedProtocol.GetRecipe(recipeId: String) =>

    case UntypedProtocol.RecipeFound(compiledRecipe: CompiledRecipe, timestamp: Long) =>

    case UntypedProtocol.NoRecipeFound(recipeId: String) =>

    //Get all recipes
    case GetAllRecipes =>

    case UntypedProtocol.RecipeInformation(compiledRecipe: CompiledRecipe, timestamp: Long)

    case UntypedProtocol.AllRecipes(recipes: Seq[RecipeInformation]) =>
  }
  */
}
