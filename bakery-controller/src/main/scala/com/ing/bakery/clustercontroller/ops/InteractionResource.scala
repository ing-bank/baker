package com.ing.bakery.clustercontroller.ops

import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.{ objFormat, envVarFormat }
import skuber.{EnvVar, NonCoreResourceSpecification, ObjectMeta, ObjectResource, ResourceDefinition}

case class InteractionResource(
    kind: String = "Interaction",
    apiVersion: String = "ing-bank.github.io/v1",
    metadata: ObjectMeta = ObjectMeta(),
    spec: InteractionResource.Spec)
  extends ObjectResource

object InteractionResource {

  case class Spec(
    image: String,
    replicas: Int,
    env: List[EnvVar],
    configMapMounts: List[ConfigMount],
    secretMounts: List[ConfigMount]
  )

  case class ConfigMount(name: String, mountPath: String)

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

  implicit val configMountFmt: Format[ConfigMount] = (
      (JsPath \ "name").format[String] and
      (JsPath \ "mountPath").format[String]
    ) (ConfigMount.apply, unlift(ConfigMount.unapply))

  implicit val interactionResourceSpecFmt: Format[Spec] = (
      (JsPath \ "image").format[String] and
      (JsPath \ "replicas").formatWithDefault[Int](1) and
      (JsPath \ "env").formatWithDefault[List[EnvVar]](List.empty) and
      (JsPath \ "configMapMounts").formatWithDefault[List[ConfigMount]](List.empty) and
      (JsPath \ "secretMounts").formatWithDefault[List[ConfigMount]](List.empty)
    ) (Spec.apply, unlift(Spec.unapply))

  implicit lazy val interactionResourceFormat: Format[InteractionResource] = (
    objFormat and
      (JsPath \ "spec").format[Spec]
    ) (apply, unlift(unapply))
}


