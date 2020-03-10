package com.ing.bakery.clustercontroller

import cats.effect.IO
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap
import org.apache.commons.codec.binary.Base64
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.{NonCoreResourceSpecification, ObjectMeta, ObjectResource, ResourceDefinition}

case class RecipeResource(
    kind: String = "Recipe",
    apiVersion: String = "ing-bank.github.io/v1",
    metadata: ObjectMeta = ObjectMeta(),
    spec:  RecipeResource.Spec)
  extends ObjectResource {

  def decodeRecipe: IO[CompiledRecipe] = {
    val decode64 = Base64.decodeBase64(spec.recipe)
    IO.fromTry(for {
      protoRecipe <- protobuf.CompiledRecipe.validate(decode64)
      recipe <- ProtoMap.ctxFromProto(protoRecipe)
    } yield recipe)
  }
}

object RecipeResource {

  def apply(recipe: CompiledRecipe, replicas: Int): RecipeResource = {
    val protoRecipe: Array[Byte] = ProtoMap.ctxToProto(recipe).toByteArray
    val encode64 = Base64.encodeBase64(protoRecipe)
    RecipeResource(spec = Spec(replicas = replicas, recipe = new String(encode64)))
  }

  case class Spec(
    bakeryVersion: String,
    replicas: Int,
    recipe: String
  )

  val specification: NonCoreResourceSpecification =
    NonCoreResourceSpecification (
      apiGroup="ing-bank.github.io",
      version="v1",
      scope = Scope.Namespaced,
      names=Names(
        plural = "recipes",
        singular = "recipe",
        kind = "Recipe",
        shortNames = List("re")
      )
    )

  implicit val resourceDefinitionRecipeResource: ResourceDefinition[RecipeResource] =
    new ResourceDefinition[RecipeResource] { def spec: NonCoreResourceSpecification = specification }

  implicit val recipeResourceSpecFmt: Format[Spec] = (
    (JsPath \ "bakeryVersion").format[String] and
    (JsPath \ "replicas").formatWithDefault[Int](1) and
    (JsPath \ "recipe").format[String]
  )(Spec.apply, unlift(Spec.unapply))

  implicit lazy val recipeResourceFormat: Format[RecipeResource] = (
    objFormat and
    (JsPath \ "spec").format[Spec]
  )(apply, unlift(unapply))
}
