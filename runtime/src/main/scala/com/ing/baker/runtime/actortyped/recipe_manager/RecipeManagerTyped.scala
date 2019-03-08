package com.ing.baker.runtime.actortyped.recipe_manager

import akka.actor.typed.{ActorRef, Behavior}
import akka.event.EventStream
import akka.persistence.typed.scaladsl.{Effect, EventSourcedBehavior, ReplyEffect}
import akka.persistence.typed.{ExpectingReply, PersistenceId}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.serialization.BakerProtoMessage
import com.ing.baker.runtime.core.events.{RecipeAdded => CoreRecipeAdded}

object RecipeManagerTyped {

  sealed trait Command extends ExpectingReply[Reply] with BakerProtoMessage

  sealed trait Reply extends BakerProtoMessage

  /** Add a recipe */
  case class AddRecipe(compiledRecipe: CompiledRecipe)(override val replyTo: ActorRef[Reply]) extends Command

  case class AddRecipeResponse(recipeId: String) extends Reply

  /** Get a specific recipe */
  case class GetRecipe(recipeId: String)(override val replyTo: ActorRef[Reply]) extends Command

  sealed trait GetRecipeResponse extends Reply

  case class RecipeFound(compiledRecipe: CompiledRecipe, timestamp: Long) extends GetRecipeResponse

  case class NoRecipeFound(recipeId: String) extends GetRecipeResponse

  /** Get all recipes */
  case class GetAllRecipes(override val replyTo: ActorRef[Reply]) extends Command

  case class AllRecipes(recipes: Seq[RecipeInformation]) extends Reply

  case class RecipeInformation(compiledRecipe: CompiledRecipe, timestamp: Long) extends BakerProtoMessage

  /** Only event */
  case class RecipeAdded(compiledRecipe: CompiledRecipe, timeStamp: Long)

  type Recipes = Map[String, (CompiledRecipe, Long)]

  val persistenceId: PersistenceId = PersistenceId("TypedRecipeManager")

  def behaviour(eventStream: EventStream): Behavior[Command] =
    EventSourcedBehavior.withEnforcedReplies[Command, RecipeAdded, Recipes](
      persistenceId = persistenceId,
      emptyState = Map.empty[String, (CompiledRecipe, Long)],
      commandHandler = commandHandler(eventStream),
      eventHandler = eventHandler
    )

  private def commandHandler(eventStream: EventStream)(recipes: Recipes, command: Command): ReplyEffect[RecipeAdded, Recipes] =
    command match {
      case add: AddRecipe =>
        addRecipe(eventStream, recipes, add)
      case get: GetRecipe =>
        getRecipe(recipes, get)
      case all: GetAllRecipes =>
        getAllRecipes(recipes, all)
    }

  private def addRecipe(eventStream: EventStream, state: Recipes, command: AddRecipe): ReplyEffect[RecipeAdded, Recipes] = {
    val recipe = command.compiledRecipe
    hasCompiledRecipe(state, recipe) match {
      case Some(recipeId) =>
        Effect.reply(command)(AddRecipeResponse(recipeId))
      case None =>
        val timestamp = System.currentTimeMillis()
        val response = AddRecipeResponse(recipe.recipeId)
        val publicEvent = CoreRecipeAdded(recipe.name, recipe.recipeId, timestamp, recipe)
        Effect
          .persist(RecipeAdded(recipe, timestamp))
          .thenRun((_: Recipes) => eventStream.publish(publicEvent))
          .thenReply(command)(_ => response)
    }
  }

  private def getRecipe(state: Recipes, command: GetRecipe): ReplyEffect[RecipeAdded, Recipes] = {
    val recipeId = command.recipeId
    state.get(recipeId) match {
      case Some((compiledRecipe, timestamp)) =>
        Effect.reply(command)(RecipeFound(compiledRecipe, timestamp))
      case None =>
        Effect.reply(command)(NoRecipeFound(recipeId))
    }
  }

  private def eventHandler(state: Recipes, event: RecipeAdded): Recipes =
    addRecipe(state, event.compiledRecipe, event.timeStamp)

  private def getAllRecipes(state: Recipes, command: GetAllRecipes): ReplyEffect[RecipeAdded, Recipes] =
    Effect.reply(command)(AllRecipes(recipesInfo(state)))

  private def hasCompiledRecipe(recipes: Recipes, compiledRecipe: CompiledRecipe): Option[String] =
    recipes.collectFirst { case (recipeId, (`compiledRecipe`, _)) =>  recipeId}

  private def addRecipe(recipes: Recipes, compiledRecipe: CompiledRecipe, timestamp: Long): Recipes =
    recipes + (compiledRecipe.recipeId -> (compiledRecipe, timestamp))

  private def recipesInfo(recipes: Recipes): Seq[RecipeInformation] =
    recipes.map { case (_, (compiledRecipe, timestamp)) => RecipeInformation(compiledRecipe, timestamp) }.toSeq


}
