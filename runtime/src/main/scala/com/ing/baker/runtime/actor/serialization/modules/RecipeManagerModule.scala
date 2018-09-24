package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.il
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol, protobuf}
import com.ing.baker.runtime.actor.{recipe_manager, protobuf => ilp}

class RecipeManagerModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case RecipeManager.RecipeAdded(recipeId, compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeAdded(Option(recipeId), Option(compiledRecipeProto))

    case RecipeManagerProtocol.AddRecipe(compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.AddRecipe(Option(compiledRecipeProto))

    case RecipeManagerProtocol.AddRecipeResponse(recipeId) =>
      protobuf.AddRecipeResponse(Option(recipeId))

    case RecipeManagerProtocol.GetRecipe(recipeId) =>
      protobuf.GetRecipe(Option(recipeId))

    case RecipeManagerProtocol.RecipeFound(compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeFound(Option(compiledRecipeProto))

    case RecipeManagerProtocol.NoRecipeFound(recipeId) =>
      protobuf.NoRecipeFound(Option(recipeId))

    case RecipeManagerProtocol.GetAllRecipes =>
      protobuf.GetAllRecipes()

    case RecipeManagerProtocol.AllRecipes(compiledRecipeMap) =>
      val compiledRecipeProtoMap = compiledRecipeMap mapValues(ctx.toProto[ilp.CompiledRecipe](_))
      protobuf.AllRecipes(compiledRecipeProtoMap)
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case recipe_manager.protobuf.RecipeAdded(Some(recipeId), Some(compiledRecipeMsg)) =>
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManager.RecipeAdded(recipeId, compiledRecipe)

    case recipe_manager.protobuf.AddRecipe(Some(compiledRecipeMsg)) =>
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManagerProtocol.AddRecipe(compiledRecipe)

    case recipe_manager.protobuf.AddRecipeResponse(Some(recipeId)) =>
      RecipeManagerProtocol.AddRecipeResponse(recipeId)

    case protobuf.GetRecipe(Some(recipeId)) =>
      RecipeManagerProtocol.GetRecipe(recipeId)

    case recipe_manager.protobuf.RecipeFound(Some(compiledRecipeMsg)) =>
      val compiledRecipe = ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)
      RecipeManagerProtocol.RecipeFound(compiledRecipe)

    case protobuf.NoRecipeFound(Some(recipeId)) =>
      RecipeManagerProtocol.NoRecipeFound(recipeId)

    case protobuf.GetAllRecipes() =>
      RecipeManagerProtocol.GetAllRecipes

    case protobuf.AllRecipes(compiledRecipesMsg) =>
      val compiledRecipes = compiledRecipesMsg mapValues(ctx.toDomain[il.CompiledRecipe](_))
      RecipeManagerProtocol.AllRecipes(compiledRecipes)
  }
}
