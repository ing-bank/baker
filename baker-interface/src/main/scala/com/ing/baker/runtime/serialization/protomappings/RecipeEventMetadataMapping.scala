package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.scaladsl.RecipeEventMetadata
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.versioned

import scala.util.Try

class RecipeEventMetadataMapping extends ProtoMap[RecipeEventMetadata, proto.RecipeEventMetadata] {

  val companion = proto.RecipeEventMetadata

  def toProto(a: RecipeEventMetadata): proto.RecipeEventMetadata = {
    proto.RecipeEventMetadata(Some(a.recipeId), Some(a.recipeName), Some(a.recipeInstanceId))
  }

  def fromProto(message: proto.RecipeEventMetadata): Try[RecipeEventMetadata] =
    for {
      recipeId <- versioned(message.recipeId, "recipeId")
      recipeName <- versioned(message.recipeName, "recipeName")
      recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
    } yield RecipeEventMetadata(recipeId, recipeName, recipeInstanceId)
}
