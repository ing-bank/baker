package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.il
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol, protobuf}
import com.ing.baker.runtime.actor.{recipe_manager, protobuf => ilp}

class RecipeManagerModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case RecipeManager.RecipeAdded(recipeId, compiledRecipe, timeStamp) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeAdded(Option(recipeId), Option(compiledRecipeProto), Option(timeStamp))

    case RecipeManagerProtocol.AddRecipe(compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.AddRecipe(Option(compiledRecipeProto))

    case RecipeManagerProtocol.AddRecipeResponse(recipeId) =>
      protobuf.AddRecipeResponse(Option(recipeId))

    case RecipeManagerProtocol.GetRecipe(recipeId) =>
      protobuf.GetRecipe(Option(recipeId))

    case RecipeManagerProtocol.RecipeFound(compiledRecipe, timestamp) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeFound(Option(compiledRecipeProto), Option(timestamp))

    case RecipeManagerProtocol.NoRecipeFound(recipeId) =>
      protobuf.NoRecipeFound(Option(recipeId))

    case RecipeManagerProtocol.GetAllRecipes =>
      protobuf.GetAllRecipes()

    case RecipeManagerProtocol.RecipeInformation(recipeId, compiledRecipe, timestamp) =>
      protobuf.RecipeEntry(Some(recipeId), Some(ctx.toProto[ilp.CompiledRecipe](compiledRecipe)), Some(timestamp))

    case RecipeManagerProtocol.AllRecipes(recipes: Seq[RecipeManagerProtocol.RecipeInformation]) =>
      protobuf.AllRecipes(recipes.map(ctx.toProto[protobuf.RecipeEntry]))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case recipe_manager.protobuf.RecipeAdded(Some(recipeId), Some(compiledRecipeMsg), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManager.RecipeAdded(recipeId, compiledRecipe, timestamp)

    case recipe_manager.protobuf.AddRecipe(Some(compiledRecipeMsg)) =>
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManagerProtocol.AddRecipe(compiledRecipe)

    case recipe_manager.protobuf.AddRecipeResponse(Some(recipeId)) =>
      RecipeManagerProtocol.AddRecipeResponse(recipeId)

    case protobuf.GetRecipe(Some(recipeId)) =>
      RecipeManagerProtocol.GetRecipe(recipeId)

    case recipe_manager.protobuf.RecipeFound(Some(compiledRecipeMsg), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManagerProtocol.RecipeFound(compiledRecipe, timestamp)

    case protobuf.NoRecipeFound(Some(recipeId)) =>
      RecipeManagerProtocol.NoRecipeFound(recipeId)

    case protobuf.GetAllRecipes() =>
      RecipeManagerProtocol.GetAllRecipes

    case protobuf.RecipeEntry(Some(recipeId), Some(compiledRecipe), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      RecipeManagerProtocol.RecipeInformation(recipeId, ctx.toDomain[il.CompiledRecipe](compiledRecipe), timestamp)

    case protobuf.AllRecipes(compiledRecipes: Seq[protobuf.RecipeEntry]) =>
      RecipeManagerProtocol.AllRecipes(compiledRecipes.map(ctx.toDomain[RecipeManagerProtocol.RecipeInformation]))
  }
}
