package com.ing.baker.runtime.actortyped.serialization.modules

import com.ing.baker.il
import com.ing.baker.runtime.actortyped.recipe_manager.{RecipeManagerTyped, protobuf}
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.actor.{protobuf => ilp}

// TODO: Temporal until new serialization refactoring is finished
class RecipeManagerTypedModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case RecipeManagerTyped.RecipeAdded(compiledRecipe, timeStamp) =>
      val compiledRecipeProto = ctx.toProto[ilp.CompiledRecipe](compiledRecipe)
      protobuf.RecipeAddedTyped(None, Some(compiledRecipeProto), Some(timeStamp))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.RecipeAddedTyped(optionalRecipeId, Some(compiledRecipeMsg), optionalTimestamp) =>
      val timestamp = optionalTimestamp.getOrElse(0l)
      val compiledRecipe =
        ctx.toDomain[il.CompiledRecipe](compiledRecipeMsg)

      // in case there was a recipe id persisted we update it with that one
      val recipeWithCorrectRecipeId = compiledRecipe.copy(recipeId = optionalRecipeId.getOrElse(compiledRecipe.recipeId))

      RecipeManagerTyped.RecipeAdded(recipeWithCorrectRecipeId, timestamp)
  }
}
