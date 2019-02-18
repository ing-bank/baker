package com.ing.baker.runtime.actortyped.recipe_manager

import RecipeManagerTyped._
import akka.actor.typed.ActorRefResolver
import com.ing.baker.runtime.actortyped.serialization.BinarySerializable
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{ toProto, fromProto, versioned }

import scala.util.Try

object RecipeManagerSerialization {

  // case class RecipeAdded(compiledRecipe: CompiledRecipe, timeStamp: Long) extends BakerProtoMessage
  object RecipeAddedSerialization extends BinarySerializable {

    type Type = RecipeAdded

    override val tag: Class[RecipeAdded] =
      classOf[RecipeAdded]
    
    override val manifest: String =
      "typed.RecipeManager.RecipeAdded"

    override def toBinary(a: RecipeAdded): Array[Byte] =
      protobuf.RecipeAddedTyped(None, Some(toProto(a.compiledRecipe)), Some(a.timeStamp)).toByteArray

    override def fromBinary(binary: Array[Byte], resolver: ActorRefResolver): Try[RecipeAdded] =
      for {
        protodes <- Try(protobuf.RecipeAddedTyped.parseFrom(binary))
        protorecipe <- versioned(protodes.compiledRecipe)("compiledRecipe")
        timeStamp <- versioned(protodes.timeStamp)("timeStamp")
        recipe <- fromProto(protorecipe)
      } yield RecipeAdded(recipe, timeStamp)
  }

}
