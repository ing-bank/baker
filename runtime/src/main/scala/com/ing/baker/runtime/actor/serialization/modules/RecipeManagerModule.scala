package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.il
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.{protobuf, recipe_manager}

class RecipeManagerModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapterContext): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case RecipeManager.RecipeAdded(recipeId, compiledRecipe) =>
      val compiledRecipeProto = ctx.toProtoType[protobuf.CompiledRecipe](compiledRecipe)
      recipe_manager.protobuf.RecipeAdded(Option(recipeId), Option(compiledRecipeProto))

  }

  override def toDomain(ctx: ProtoEventAdapterContext): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case recipe_manager.protobuf.RecipeAdded(Some(recipeId), Some(compiledRecipeMsg)) =>

      val compiledRecipe = ctx.toDomainType[il.CompiledRecipe](compiledRecipeMsg)
      RecipeAdded(recipeId, compiledRecipe)
  }

}
