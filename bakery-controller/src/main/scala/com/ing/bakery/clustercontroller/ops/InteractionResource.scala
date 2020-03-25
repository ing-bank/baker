package com.ing.bakery.clustercontroller.ops

import play.api.libs.functional.syntax.{unlift, _}
import play.api.libs.json.{Format, JsPath}
import skuber.ResourceSpecification.{Names, Scope}
import skuber.json.format.objFormat
import skuber.{NonCoreResourceSpecification, ObjectMeta, ObjectResource, ResourceDefinition}

case class InteractionResource(
                                kind: String = "Interaction",
                                apiVersion: String = "ing-bank.github.io/v1",
                                metadata: ObjectMeta = ObjectMeta(),
                                spec: InteractionResource.Spec)
  extends ObjectResource

object InteractionResource {

  case class Spec(
                   image: String,
                   replicas: Int
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
      (JsPath \ "replicas").formatWithDefault[Int](1)
    ) (Spec.apply, unlift(Spec.unapply))

  implicit lazy val interactionResourceFormat: Format[InteractionResource] = (
    objFormat and
      (JsPath \ "spec").format[Spec]
    ) (apply, unlift(unapply))
}


