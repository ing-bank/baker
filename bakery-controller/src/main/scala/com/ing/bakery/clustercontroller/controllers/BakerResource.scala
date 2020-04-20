package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import org.apache.commons.codec.binary.Base64
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.{ConfigMap, NonCoreResourceSpecification, ObjectMeta, ObjectResource, ResourceDefinition}

import scala.util.Try

case class BakerResource(
    kind: String = "Baker",
    apiVersion: String = "ing-bank.github.io/v1",
    metadata: ObjectMeta = ObjectMeta(),
    spec:  BakerResource.Spec)
  extends ObjectResource {

  val recipes: Try[List[(String, CompiledRecipe)]] = {
    spec.recipes.traverse { serializedRecipe =>
      val decode64 = Base64.decodeBase64(serializedRecipe)
      for {
        protoRecipe <- protobuf.CompiledRecipe.validate(decode64)
        recipe <- ProtoMap.ctxFromProto(protoRecipe)
      } yield serializedRecipe -> recipe
    }
  }
}

object BakerResource {

  def fromConfigMap(configMap: ConfigMap): FromConfigMapValidation[BakerResource] = {
    ( Utils.extractValidated(configMap, "bakeryVersion")
    , Utils.extractAndParseValidated(configMap, "replicas", r => Try(r.toInt)).orElse(2.validNel): FromConfigMapValidation[Int]
    , Utils.extractListValidated(configMap, "recipes")
    ).mapN(Spec).map(spec => BakerResource(spec = spec))
  }

  case class Spec(
    bakeryVersion: String,
    replicas: Int,
    recipes: List[String]
  )

  val specification: NonCoreResourceSpecification =
    NonCoreResourceSpecification (
      apiGroup = "ing-bank.github.io",
      version = "v1",
      scope = Scope.Namespaced,
      names=Names(
        plural = "bakers",
        singular = "baker",
        kind = "Baker",
        shortNames = List("ba")
      )
    )

  implicit val resourceDefinitionRecipeResource: ResourceDefinition[BakerResource] =
    new ResourceDefinition[BakerResource] { def spec: NonCoreResourceSpecification = specification }

  implicit val recipeResourceSpecFmt: Format[Spec] = (
    (JsPath \ "bakeryVersion").format[String] and
    (JsPath \ "replicas").formatWithDefault[Int](2) and
    (JsPath \ "recipes").format[List[String]]
  )(Spec.apply, unlift(Spec.unapply))

  implicit lazy val recipeResourceFormat: Format[BakerResource] = (
    objFormat and
    (JsPath \ "spec").format[Spec]
  )(apply, unlift(unapply))
}
