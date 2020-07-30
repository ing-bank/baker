package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.{envVarFormat, objFormat, resRqtsFormat}
import skuber.{ConfigMap, EnvVar, NonCoreResourceSpecification, ObjectMeta, ObjectResource, Resource, ResourceDefinition}

import scala.util.Try

case class InteractionResource(
    kind: String = "Interaction",
    apiVersion: String = "ing-bank.github.io/v1",
    metadata: ObjectMeta = ObjectMeta(),
    spec: InteractionResource.Spec)
  extends ObjectResource

object InteractionResource {

  def fromConfigMap(configMap: ConfigMap): FromConfigMapValidation[InteractionResource] = {

    def envValidated: FromConfigMapValidation[List[EnvVar]] = {

      def envFromLiteral(sub: ConfigMap): FromConfigMapValidation[EnvVar] =
        ( Utils.extractValidatedString(sub, "name")
        , Utils.extractValidatedString(sub, "value")
        ).mapN((name, value) => EnvVar(name, EnvVar.StringValue(value)))

      def envFromConfigMap(sub: ConfigMap): FromConfigMapValidation[EnvVar] =
        ( Utils.extractValidatedString(sub, "name")
        , Utils.extractValidatedString(sub, "valueFrom.configMapKeyRef.name")
        , Utils.extractValidatedString(sub, "valueFrom.configMapKeyRef.key")
        ).mapN((name, configMapName, key) => EnvVar(name, EnvVar.ConfigMapKeyRef(key = key, name = configMapName)))

      def envFromSecret(sub: ConfigMap): FromConfigMapValidation[EnvVar] =
        ( Utils.extractValidatedString(sub, "name")
        , Utils.extractValidatedString(sub, "valueFrom.secretKeyRef.name")
        , Utils.extractValidatedString(sub, "valueFrom.secretKeyRef.key")
        ).mapN((name, secretName, key) => EnvVar(name, EnvVar.SecretKeyRef(key = key, name = secretName)))

      Utils.extractListWithSubPaths(configMap, "env")
        .orElse(List.empty.validNel)
        .andThen(_.traverse[FromConfigMapValidation, EnvVar](sub =>
          envFromLiteral(sub)
            .orElse(envFromConfigMap(sub))
            .orElse(envFromSecret(sub))
            .orElse(s"No valid environment between subpaths '${sub.data.keys.mkString(", ")}' in ConfigMap '${sub.name}'".invalidNel)
        ))
    }

    ( Utils.extractValidatedString(configMap, "image")
    , Utils.extractValidatedStringOption(configMap, "imagePullSecret")
    , Utils.extractAndParseValidated(configMap, "replicas", r => Try(r.toInt)).orElse(1.validNel): FromConfigMapValidation[Int]
    , envValidated
    , Utils.extractListValidated(configMap, "configMapMounts")
    , Utils.extractListValidated(configMap, "secretMounts")
    , Utils.optional(Utils.resourcesFromConfigMap(configMap))
    ).mapN(Spec).map(spec => InteractionResource(metadata = configMap.metadata, spec = spec))
  }

  case class Spec(
    image: String,
    imagePullSecret: Option[String],
    replicas: Int,
    env: List[EnvVar],
    configMapMounts: List[String],
    secretMounts: List[String],
    resources: Option[Resource.Requirements]
  )

  val specification: NonCoreResourceSpecification =
    NonCoreResourceSpecification(
      apiGroup = "ing-bank.github.io",
      version = "v1",
      scope = Scope.Namespaced,
      names = Names(
        plural = "interactions",
        singular = "interaction",
        kind = "Interaction",
        shortNames = List("int")
      )
    )

  implicit val resourceDefinitionInteractionResource: ResourceDefinition[InteractionResource] =
    new ResourceDefinition[InteractionResource] {
      def spec: NonCoreResourceSpecification = specification
    }

  implicit val interactionResourceSpecFmt: Format[Spec] = (
      (JsPath \ "image").format[String] and
      (JsPath \ "imagePullSecret").formatNullableWithDefault[String](None) and
      (JsPath \ "replicas").formatWithDefault[Int](1) and
      (JsPath \ "env").formatWithDefault[List[EnvVar]](List.empty) and
      (JsPath \ "configMapMounts").formatWithDefault[List[String]](List.empty) and
      (JsPath \ "secretMounts").formatWithDefault[List[String]](List.empty) and
      (JsPath \ "resources").formatNullable[Resource.Requirements]
    ) (Spec.apply, unlift(Spec.unapply))

  implicit lazy val interactionResourceFormat: Format[InteractionResource] = (
    objFormat and
      (JsPath \ "spec").format[Spec]
    ) (apply, unlift(unapply))
}


