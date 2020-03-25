package com.ing.bakery.clustercontroller.ops

import com.ing.bakery.clustercontroller.ResourceOperations.ControllerSpecification
import skuber.ext.Deployment
import skuber.{Container, ObjectMeta, Pod, Protocol, Service}

object InteractionOperations {

  val spec: ControllerSpecification[InteractionResource] =
    ControllerSpecification(service, deployment, interactionLabel)

  def interactionLabel(interaction: InteractionResource): (String, String) = "interaction" -> interaction.name

  def serviceName(name: String): String = name + "-interaction-service"

  val baasComponentLabel: (String, String) = "baas-component" -> "remote-interaction"

  val httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  def deployment(interaction: InteractionResource): Deployment = {

    val name: String = interaction.name
    val image: String = interaction.spec.image
    val replicas: Int = interaction.spec.replicas

    val healthProbe = skuber.Probe(
      action = skuber.HTTPGetAction(
        port = Right(httpAPIPort.name),
        path = "/api/v3/health"
      )
    )

    val interactionContainer = Container(
      name = name,
      image = image)
      .exposePort(httpAPIPort)
      .withReadinessProbe(healthProbe)
      .withLivenessProbe(healthProbe)

    val podTemplate = Pod.Template.Spec
      .named(name)
      .addContainer(interactionContainer)
      .addLabel(interactionLabel(interaction))

    new Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(interactionLabel(interaction))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  def service(interaction: InteractionResource): Service = {
    Service(serviceName(interaction.name))
      .addLabel(baasComponentLabel)
      .withSelector(interactionLabel(interaction))
      .setPort(Service.Port(
        name = httpAPIPort.name,
        port = httpAPIPort.containerPort
      ))
  }
}
