package com.ing.baker.runtime.actor.recipe_manager

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider

import scala.util.Try

object RecipeManagerSerialization {

  implicit def recipeAddedProto(implicit provider: SerializersProvider): ProtoMap[RecipeAdded, protobuf.RecipeAdded] =
    new ProtoMap[RecipeAdded, protobuf.RecipeAdded] {

      val companion = protobuf.RecipeAdded

      def toProto(a: RecipeAdded): protobuf.RecipeAdded =
        protobuf.RecipeAdded(None, Option(ctxToProto(a.compiledRecipe)), Option(a.timeStamp))

      def fromProto(message: protobuf.RecipeAdded): Try[RecipeAdded] =
        for {
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timeStamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeAdded(compiledRecipe, timestamp)
    }

  implicit def addRecipeProto(implicit provider: SerializersProvider): ProtoMap[AddRecipe, protobuf.AddRecipe] =
    new ProtoMap[AddRecipe, protobuf.AddRecipe] {

      val companion = protobuf.AddRecipe

      def toProto(a: AddRecipe): protobuf.AddRecipe =
        protobuf.AddRecipe(Option(ctxToProto(a.compiledRecipe)))

      def fromProto(message: protobuf.AddRecipe): Try[AddRecipe] =
        for {
          protoCompiledRecipe <- versioned(message.compiledRecipe, "compiledRecipe")
          compiledRecipe <- ctxFromProto(protoCompiledRecipe)
        } yield AddRecipe(compiledRecipe)
    }

  implicit def addRecipeResponseProto: ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] =
    new ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] {

      val companion = protobuf.AddRecipeResponse

      def toProto(a: AddRecipeResponse): protobuf.AddRecipeResponse =
        protobuf.AddRecipeResponse(Option(a.recipeId))

      def fromProto(message: protobuf.AddRecipeResponse): Try[AddRecipeResponse] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield AddRecipeResponse(recipeId)
    }

  implicit def getRecipeProto: ProtoMap[GetRecipe, protobuf.GetRecipe] =
    new ProtoMap[GetRecipe, protobuf.GetRecipe] {

      val companion = protobuf.GetRecipe

      def toProto(a: GetRecipe): protobuf.GetRecipe =
        protobuf.GetRecipe(Option(a.recipeId))

      def fromProto(message: protobuf.GetRecipe): Try[GetRecipe] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield GetRecipe(recipeId)
    }

  implicit def recipeFoundProto(implicit provider: SerializersProvider): ProtoMap[RecipeFound, protobuf.RecipeFound] =
    new ProtoMap[RecipeFound, protobuf.RecipeFound] {

      val companion = protobuf.RecipeFound

      def toProto(a: RecipeFound): protobuf.RecipeFound =
        protobuf.RecipeFound(Option(ctxToProto(a.compiledRecipe)), Option(a.timestamp))

      def fromProto(message: protobuf.RecipeFound): Try[RecipeFound] =
        for {
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timestamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeFound(compiledRecipe, timestamp)
    }

  implicit def noRecipeFoundProto: ProtoMap[NoRecipeFound, protobuf.NoRecipeFound] =
    new ProtoMap[NoRecipeFound, protobuf.NoRecipeFound] {

      val companion = protobuf.NoRecipeFound

      def toProto(a: NoRecipeFound): protobuf.NoRecipeFound =
        protobuf.NoRecipeFound(Option(a.recipeId))

      def fromProto(message: protobuf.NoRecipeFound): Try[NoRecipeFound] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
        } yield NoRecipeFound(recipeId)
    }

  implicit def getAllRecipesProto: ProtoMap[GetAllRecipes.type, protobuf.GetAllRecipes] =
    new ProtoMap[GetAllRecipes.type, protobuf.GetAllRecipes] {

      val companion = protobuf.GetAllRecipes

      def manifest: String = "RecipeManagerProtocol.GetAllRecipes"

      def toProto(a: GetAllRecipes.type): protobuf.GetAllRecipes =
        protobuf.GetAllRecipes()

      def fromProto(message: protobuf.GetAllRecipes): Try[GetAllRecipes.type] =
        Try(GetAllRecipes)
    }

  implicit def recipeInformationProto(implicit provider: SerializersProvider): ProtoMap[RecipeInformation, protobuf.RecipeEntry] =
    new ProtoMap[RecipeInformation, protobuf.RecipeEntry] {

      val companion = protobuf.RecipeEntry

      override def toProto(a: RecipeInformation): protobuf.RecipeEntry =
        protobuf.RecipeEntry(None, Option(ctxToProto(a.compiledRecipe)), Option(a.timestamp))

      override def fromProto(message: protobuf.RecipeEntry): Try[RecipeInformation] =
        for {
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          timestamp <- versioned(message.timestamp, "timestamp")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeInformation(compiledRecipe, timestamp)
    }

  implicit def allRecipesProto(implicit provider: SerializersProvider): ProtoMap[AllRecipes, protobuf.AllRecipes] =
    new ProtoMap[AllRecipes, protobuf.AllRecipes] {

      val companion = protobuf.AllRecipes

      def manifest: String = "RecipeManagerProtocol.AllRecipes"

      def toProto(a: AllRecipes): protobuf.AllRecipes =
        protobuf.AllRecipes(a.recipes.map(ctxToProto(_)))

      def fromProto(message: protobuf.AllRecipes): Try[AllRecipes] =
        for {
          recipes <- message.recipeEntries.toList.traverse(ctxFromProto(_))
        } yield AllRecipes(recipes)
    }
}
