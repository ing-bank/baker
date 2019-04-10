package com.ing.baker.runtime.actor.recipe_manager

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actortyped.serialization.{BinarySerializable, ProtobufMapping}
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{versioned, fromProto => ctxFromProto, toProto => ctxToProto}
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider

import scala.util.Try

object RecipeManagerSerialization {

  def recipeAddedSerializer(implicit provider: SerializersProvider): BinarySerializable =
    new BinarySerializable {

      type Type = RecipeAdded

      val tag: Class[RecipeAdded] = classOf[RecipeAdded]

      def manifest: String = "RecipeManager.RecipeAdded"

      def toBinary(a: RecipeAdded): Array[Byte] =
        protobuf.RecipeAdded(None, Option(ctxToProto(a.compiledRecipe)), Option(a.timeStamp)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[RecipeAdded] =
        for {
          message <- Try(protobuf.RecipeAdded.parseFrom(binary))
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timeStamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeAdded(compiledRecipe, timestamp)
    }

  def addRecipeSerializer(implicit provider: SerializersProvider): BinarySerializable =
    new BinarySerializable {

      type Type = AddRecipe

      val tag: Class[AddRecipe] = classOf[AddRecipe]

      def manifest: String = "RecipeManagerProtocol.AddRecipe"

      def toBinary(a: AddRecipe): Array[Byte] =
        protobuf.AddRecipe(Option(ctxToProto(a.compiledRecipe))).toByteArray

      def fromBinary(binary: Array[Byte]): Try[AddRecipe] =
        for {
          message <- Try(protobuf.AddRecipe.parseFrom(binary))
          protoCompiledRecipe <- versioned(message.compiledRecipe, "compiledRecipe")
          compiledRecipe <- ctxFromProto(protoCompiledRecipe)
        } yield AddRecipe(compiledRecipe)
    }

  def addRecipeResponseSerializer: BinarySerializable =
    new BinarySerializable {

      type Type = AddRecipeResponse

      val tag: Class[AddRecipeResponse] = classOf[AddRecipeResponse]

      def manifest: String = "RecipeManagerProtocol.AddRecipeResponse"

      def toBinary(a: AddRecipeResponse): Array[Byte] =
        protobuf.AddRecipeResponse(Option(a.recipeId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[AddRecipeResponse] =
        for {
          message <- Try(protobuf.AddRecipeResponse.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield AddRecipeResponse(recipeId)
    }

  def getRecipeSerializer: BinarySerializable =
    new BinarySerializable {

      type Type = GetRecipe

      val tag: Class[GetRecipe] = classOf[GetRecipe]

      def manifest: String = "RecipeManagerProtocol.GetRecipe"

      def toBinary(a: GetRecipe): Array[Byte] =
        protobuf.GetRecipe(Option(a.recipeId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[GetRecipe] =
        for {
          message <- Try(protobuf.GetRecipe.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield GetRecipe(recipeId)
    }

  def recipeFoundSerializer(implicit provider: SerializersProvider): BinarySerializable =
    new BinarySerializable {

      type Type = RecipeFound

      val tag: Class[RecipeFound] = classOf[RecipeFound]

      def manifest: String = "RecipeManagerProtocol.RecipeFound"

      def toBinary(a: RecipeFound): Array[Byte] =
        protobuf.RecipeFound(Option(ctxToProto(a.compiledRecipe)), Option(a.timestamp)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[RecipeFound] =
        for {
          message <- Try(protobuf.RecipeFound.parseFrom(binary))
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timestamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeFound(compiledRecipe, timestamp)
    }

  def noRecipeFoundSerializer: BinarySerializable =
    new BinarySerializable {

      type Type = NoRecipeFound

      val tag: Class[NoRecipeFound] = classOf[NoRecipeFound]

      def manifest: String = "RecipeManagerProtocol.NoRecipeFound"

      def toBinary(a: NoRecipeFound): Array[Byte] =
        protobuf.NoRecipeFound(Option(a.recipeId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[NoRecipeFound] =
        for {
          message <- Try(protobuf.NoRecipeFound.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield NoRecipeFound(recipeId)
    }

  def getAllRecipesSerializer: BinarySerializable =
    new BinarySerializable {

      type Type = GetAllRecipes.type

      val tag: Class[_ <: Type] = GetAllRecipes.getClass

      def manifest: String = "RecipeManagerProtocol.GetAllRecipes"

      def toBinary(a: GetAllRecipes.type): Array[Byte] =
        protobuf.GetAllRecipes().toByteArray

      def fromBinary(binary: Array[Byte]): Try[GetAllRecipes.type] =
        Try(GetAllRecipes)
    }

  implicit def recipeInformationProto(implicit provider: SerializersProvider): ProtobufMapping[RecipeInformation, protobuf.RecipeEntry] =
    new ProtobufMapping[RecipeInformation, protobuf.RecipeEntry] {

      override def toProto(a: RecipeInformation): protobuf.RecipeEntry =
        protobuf.RecipeEntry(None, Option(ctxToProto(a.compiledRecipe)), Option(a.timestamp))

      override def fromProto(message: protobuf.RecipeEntry): Try[RecipeInformation] =
        for {
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timestamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeInformation(compiledRecipe, timestamp)
    }

  def allRecipesSerializer(implicit provider: SerializersProvider): BinarySerializable =
    new BinarySerializable {

      type Type = AllRecipes

      val tag: Class[AllRecipes] = classOf[AllRecipes]

      def manifest: String = "RecipeManagerProtocol.AllRecipes"

      def toBinary(a: AllRecipes): Array[Byte] =
        protobuf.AllRecipes(a.recipes.map(ctxToProto(_))).toByteArray

      def fromBinary(binary: Array[Byte]): Try[AllRecipes] =
        for {
          message <- Try(protobuf.AllRecipes.parseFrom(binary))
          recipes <- message.recipeEntries.toList.traverse(ctxFromProto(_))
        } yield AllRecipes(recipes)
    }
}
