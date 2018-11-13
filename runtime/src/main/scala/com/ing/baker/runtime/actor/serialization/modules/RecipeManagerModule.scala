package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.il
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol, protobuf}
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.actor.{recipe_manager, protobuf => ilp}

class RecipeManagerModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case RecipeManager.RecipeAdded(compiledRecipe, timeStamp) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeAdded(None, Some(compiledRecipeProto), Some(timeStamp))

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

    case RecipeManagerProtocol.RecipeInformation(compiledRecipe, timestamp) =>
      protobuf.RecipeEntry(None, Some(ctx.toProto[ilp.CompiledRecipe](compiledRecipe)), Some(timestamp))

    case RecipeManagerProtocol.AllRecipes(recipes: Seq[RecipeManagerProtocol.RecipeInformation]) =>
      protobuf.AllRecipes(recipes.map(ctx.toProto[protobuf.RecipeEntry]))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case recipe_manager.protobuf.RecipeAdded(optionalRecipeId, Some(compiledRecipeMsg), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      val compiledRecipe =
        ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)

      // in case there was a recipe id persisted we update it with that one
      val recipeWithCorrectRecipeId = compiledRecipe.copy(recipeId = optionalRecipeId.getOrElse(compiledRecipe.recipeId))

      RecipeManager.RecipeAdded(recipeWithCorrectRecipeId, timestamp)

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

    case protobuf.RecipeEntry(optionalRecipeId, Some(protoRecipe), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](protoRecipe)

      // in case a recipe id was persisted we prefer it over the computed one
      val compiledRecipeWithUpdatedRecipeId = optionalRecipeId.map(id => compiledRecipe.copy(recipeId = id)).getOrElse(compiledRecipe)

      RecipeManagerProtocol.RecipeInformation(compiledRecipeWithUpdatedRecipeId, timestamp)

    case protobuf.AllRecipes(compiledRecipes: Seq[protobuf.RecipeEntry]) =>
      RecipeManagerProtocol.AllRecipes(compiledRecipes.map(ctx.toDomain[RecipeManagerProtocol.RecipeInformation]))
  }
}
