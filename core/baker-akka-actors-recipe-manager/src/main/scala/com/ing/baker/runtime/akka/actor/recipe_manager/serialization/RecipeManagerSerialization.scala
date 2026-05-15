package com.ing.baker.runtime.akka.actor.recipe_manager.serialization

import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProto._
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}

/**
 * Provides serialization entries for RecipeManager actor messages.
 * 
 * This object is responsible for defining how RecipeManager-related messages
 * are serialized to protobuf format. It owns the serialization logic for all
 * RecipeManagerProtocol messages.
 */
object RecipeManagerSerialization {

  /**
   * Returns the list of serialization entries for RecipeManager messages.
   * 
   * @param serializerProvider Provides access to Akka's serialization system
   * @return List of BinarySerializable entries for RecipeManager messages
   */
  def entries(implicit serializerProvider: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[RecipeManagerProtocol.AddRecipe]
        .register("RecipeManagerProtocol.AddRecipe"),
      forType[RecipeManagerProtocol.AddRecipeResponse]
        .register("RecipeManagerProtocol.AddRecipeResponse"),
      forType[RecipeManagerProtocol.GetRecipe]
        .register("RecipeManagerProtocol.GetRecipe"),
      forType[RecipeManagerProtocol.RecipeFound]
        .register("RecipeManagerProtocol.RecipeFound"),
      forType[RecipeManagerProtocol.NoRecipeFound]
        .register("RecipeManagerProtocol.NoRecipeFound"),
      forType[RecipeManagerProtocol.GetAllRecipes.type]
        .register("RecipeManagerProtocol.GetAllRecipes"),
      forType[RecipeManagerProtocol.AllRecipes]
        .register("RecipeManagerProtocol.AllRecipes"),
      forType[RecipeManagerProtocol.RecipeAdded]
        .register("RecipeManager.RecipeAdded")
    )
}
