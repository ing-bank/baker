package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import org.apache.commons.codec.binary.Base64
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.Resource
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.json.format.resRqtsFormat
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

    ( Utils.extractValidatedString(configMap, "image")
    , Utils.extractValidatedStringOption(configMap, "imagePullSecret")
    , Utils.extractValidatedStringOption(configMap, "serviceAccountSecret")
    , Utils.extractValidatedStringOption(configMap, "kafkaBootstrapServers")
    , Utils.extractAndParseValidated(configMap, "replicas", r => Try(r.toInt)).orElse(2.validNel): FromConfigMapValidation[Int]
    , Utils.extractListValidated(configMap, "recipes")
    , Utils.optional(Utils.resourcesFromConfigMap(configMap))
    , Utils.extractValidatedStringOption(configMap, "config")
    , Utils.extractValidatedStringOption(configMap, "secrets")
    ).mapN(Spec).map(spec => BakerResource(metadata = configMap.metadata, spec = spec))
  }

  case class Spec(
    image: String,
    imagePullSecret: Option[String],
    serviceAccountSecret: Option[String],
    kafkaBootstrapServers: Option[String],
    replicas: Int,
    recipes: List[String],
    resources: Option[Resource.Requirements],
    config: Option[String],
    secrets: Option[String]
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
    (JsPath \ "image").format[String] and
    (JsPath \ "imagePullSecret").formatNullableWithDefault[String](None) and
    (JsPath \ "serviceAccountSecret").formatNullableWithDefault[String](None) and
    (JsPath \ "kafkaBootstrapServers").formatNullableWithDefault[String](None) and
    (JsPath \ "replicas").formatWithDefault[Int](2) and
    (JsPath \ "recipes").format[List[String]] and
    (JsPath \ "resources").formatNullableWithDefault[Resource.Requirements](None) and
    (JsPath \ "config").formatNullableWithDefault[String](None) and
    (JsPath \ "secrets").formatNullableWithDefault[String](None)
  )(Spec.apply, unlift(Spec.unapply))

  implicit lazy val recipeResourceFormat: Format[BakerResource] = (
    objFormat and
    (JsPath \ "spec").format[Spec]
  )(apply, unlift(unapply))
}
