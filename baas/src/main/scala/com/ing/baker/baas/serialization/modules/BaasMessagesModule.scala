package com.ing.baker.baas.serialization.modules

import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.baas.server.protocol
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.actor.{protobuf => bakerProto}

class BaasMessagesModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case protocol.AddInteractionHTTPRequest(name, uri, inputTypes) =>
      val inputTypesProto = inputTypes.map(ctx.toProto[bakerProto.Type])
      protobuf.AddInteractionHTTPRequest(Some(name), Some(uri), inputTypesProto)

    case protocol.AddInteractionHTTPResponse(description) =>
      protobuf.AddInteractionHTTPResponse(Some(description))

    case protocol.AddRecipeRequest(compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[bakerProto.CompiledRecipe](compiledRecipe)
      protobuf.AddRecipeRequest(Some(compiledRecipeProto))

    case protocol.AddRecipeResponse(recipeId) =>
      protobuf.AddRecipeResponse(Some(recipeId))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.AddInteractionHTTPRequest(Some(name), Some(uri), inputTypesProto) =>
      val inputTypes = inputTypesProto.map(ctx.toDomain[com.ing.baker.types.Type])
      protocol.AddInteractionHTTPRequest(name, uri, inputTypes)

    case protobuf.AddInteractionHTTPResponse(Some(description)) =>
      protocol.AddInteractionHTTPResponse(description)

    case protobuf.AddRecipeRequest(Some(compiledRecipeProto)) =>
      val compiledRecipe = ctx.toDomain[CompiledRecipe](compiledRecipeProto)
      protocol.AddRecipeRequest(compiledRecipe)

    case protobuf.AddRecipeResponse(Some(recipeId)) =>
      protocol.AddRecipeResponse(recipeId)
  }
}
