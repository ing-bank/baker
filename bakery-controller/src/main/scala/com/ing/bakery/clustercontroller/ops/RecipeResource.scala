package com.ing.bakery.clustercontroller.ops

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap
import org.apache.commons.codec.binary.Base64
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.{NonCoreResourceSpecification, ObjectMeta, ObjectResource, ResourceDefinition}

import scala.util.Try

case class RecipeResource(
    kind: String = "Recipe",
    apiVersion: String = "ing-bank.github.io/v1",
    metadata: ObjectMeta = ObjectMeta(),
    spec:  RecipeResource.Spec)
  extends ObjectResource {

  val recipe: Try[CompiledRecipe] = {
    val decode64 = Base64.decodeBase64(spec.recipe)
    for {
      protoRecipe <- protobuf.CompiledRecipe.validate(decode64)
      recipe <- ProtoMap.ctxFromProto(protoRecipe)
    } yield recipe
  }

  val recipeId: Try[String] =
    recipe.map(_.recipeId)
}

object RecipeResource {

  case class Spec(
    bakeryVersion: String,
    replicas: Int,
    recipe: String
  )

  val specification: NonCoreResourceSpecification =
    NonCoreResourceSpecification (
      apiGroup = "ing-bank.github.io",
      version = "v1",
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
    (JsPath \ "replicas").formatWithDefault[Int](2) and
    (JsPath \ "recipe").format[String]
  )(Spec.apply, unlift(Spec.unapply))

  implicit lazy val recipeResourceFormat: Format[RecipeResource] = (
    objFormat and
    (JsPath \ "spec").format[Spec]
  )(apply, unlift(unapply))
}
