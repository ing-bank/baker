package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import org.apache.commons.codec.binary.Base64
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.{ConfigMap, NonCoreResourceSpecification, ObjectMeta, ObjectResource, Probe, Resource, ResourceDefinition}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.json.format.resRqtsFormat

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
    , Utils.extractValidatedBoolean(configMap, "apiLoggingEnabled")
    , Utils.optional(Utils.sidecarFromConfigMap(configMap))
    ).mapN(Spec).map(spec => BakerResource(metadata = configMap.metadata, spec = spec))
  }

  case class SidecarSpec(
                        image: String,
                        resources: Option[Resource.Requirements],
                        configVolumeMountPath: Option[String],
                        livenessProbe: Option[Probe],
                        readinessProbe: Option[Probe],
                        environment: Option[Map[String, String]]
                        )

  case class Spec(
    image: String,
    imagePullSecret: Option[String],
    serviceAccountSecret: Option[String],
    kafkaBootstrapServers: Option[String],
    replicas: Int,
    recipes: List[String],
    resources: Option[Resource.Requirements],
    config: Option[String],
    secrets: Option[String],
    apiLoggingEnabled: Boolean,
    sidecar: Option[SidecarSpec]
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

  implicit val probeFmt: Format[Probe] = (
    (JsPath \ "scheme" ).format[String] and
    (JsPath \ "port" ).format[String] and
    (JsPath \ "path" ).format[String]
    ) ( (scheme, port, path) => skuber.Probe(
      action = skuber.HTTPGetAction(
        schema = scheme,
        port = Right(port),
        path = path
      ),
      initialDelaySeconds = 15,
      timeoutSeconds = 10,
      failureThreshold = Some(30)
    ), unlift( _.action match {
    case action: skuber.HTTPGetAction =>
      Some(action.schema, action.port.right.getOrElse(""), action.path)
    case _ => None
  }))

  implicit val sidecarSpecFmt: Format[SidecarSpec] = (
    (JsPath \ "image").format[String] and
    (JsPath \ "resources").formatNullableWithDefault[Resource.Requirements](None) and
    (JsPath \ "configVolumeMountPath" ).formatNullable[String] and
    (JsPath \ "livenessProbe" ).formatNullableWithDefault[Probe](None) and
    (JsPath \ "readinessProbe" ).formatNullableWithDefault[Probe](None) and
    (JsPath \ "environment" ).formatNullable[Map[String, String]]
    )(SidecarSpec.apply, unlift(SidecarSpec.unapply))

  implicit val recipeResourceSpecFmt: Format[Spec] = (
    (JsPath \ "image").format[String] and
    (JsPath \ "imagePullSecret").formatNullableWithDefault[String](None) and
    (JsPath \ "serviceAccountSecret").formatNullableWithDefault[String](None) and
    (JsPath \ "kafkaBootstrapServers").formatNullableWithDefault[String](None) and
    (JsPath \ "replicas").formatWithDefault[Int](2) and
    (JsPath \ "recipes").format[List[String]] and
    (JsPath \ "resources").formatNullableWithDefault[Resource.Requirements](None) and
    (JsPath \ "config").formatNullableWithDefault[String](None) and
    (JsPath \ "secrets").formatNullableWithDefault[String](None) and
    (JsPath \ "apiLoggingEnabled").formatWithDefault[Boolean](false) and
    (JsPath \ "sidecar").formatNullableWithDefault[SidecarSpec](None)
  )(Spec.apply, unlift(Spec.unapply))

  implicit lazy val recipeResourceFormat: Format[BakerResource] = (
    objFormat and
    (JsPath \ "spec").format[Spec]
  )(apply, unlift(unapply))
}
