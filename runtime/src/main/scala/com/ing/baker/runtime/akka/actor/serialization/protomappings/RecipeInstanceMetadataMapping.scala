package com.ing.baker.runtime.akka.actor.serialization.protomappings

import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.versioned
import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata

import scala.util.Try

class RecipeInstanceMetadataMapping extends ProtoMap[RecipeInstanceMetadata, proto.RecipeInstanceMetadata] {

    val companion = proto.RecipeInstanceMetadata

    def toProto(a: RecipeInstanceMetadata): proto.RecipeInstanceMetadata = {
      proto.RecipeInstanceMetadata(Some(a.recipeId), Some(a.recipeInstanceId), Some(a.createdTime))
    }

    def fromProto(message: proto.RecipeInstanceMetadata): Try[RecipeInstanceMetadata] =
      for {
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        createdTime <- versioned(message.createdTime, "createdTime")
      } yield RecipeInstanceMetadata(recipeId, recipeInstanceId, createdTime)
  }
