package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.runtime.akka.actor.{protobuf => proto}
import com.ing.baker.runtime.scaladsl.RecipeInformation
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}

import scala.util.Try

class RecipeInformationMapping extends ProtoMap[RecipeInformation, proto.RecipeInformation] {

  val companion = proto.RecipeInformation

  def toProto(a: RecipeInformation): proto.RecipeInformation = {
    proto.RecipeInformation(Some(ctxToProto(a.compiledRecipe)), Some(a.recipeCreatedTime), a.errors.toSeq)
  }

  def fromProto(message: proto.RecipeInformation): Try[RecipeInformation] =
    for {
      compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
      compiledRecipe <- ctxFromProto(compiledRecipeProto)
      recipeCreatedTime <- versioned(message.recipeCreatedTime, "recipeCreatedTime")
    } yield RecipeInformation(compiledRecipe, recipeCreatedTime, message.errors.toSet, validate = true, compiledRecipe.sensoryEvents)
}
