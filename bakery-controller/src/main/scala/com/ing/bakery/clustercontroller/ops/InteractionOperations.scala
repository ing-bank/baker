package com.ing.bakery.clustercontroller.ops

import com.ing.bakery.clustercontroller.ResourceOperations.ControllerSpecification
import skuber.ext.Deployment
import skuber.{Container, ObjectMeta, Pod, Protocol, Service, Volume}

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
      ),
      initialDelaySeconds = 10,
      timeoutSeconds = 5
    )

    val interactionContainer = Container(
      name = name,
      image = image)
      .exposePort(httpAPIPort)
      .withReadinessProbe(healthProbe)
      .withLivenessProbe(healthProbe)
      .copy(env = interaction.spec.env)
      .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")
      // todo parametrise?
      .requestMemory("256M")
      .requestCPU("200m")

    val interactionContainerWithMounts0 =
      interaction.spec.configMapMounts.foldLeft(interactionContainer) { (container, configMount) =>
        container.mount(configMount.name, configMount.mountPath, readOnly = true)
      }

    val interactionContainerWithMounts1 =
      interaction.spec.secretMounts.foldLeft(interactionContainerWithMounts0) { (container, configMount) =>
        container.mount(configMount.name, configMount.mountPath, readOnly = true)
      }

    val volumesConfigMaps =
      interaction.spec.configMapMounts.map { configMount =>
        Volume(configMount.name, Volume.ConfigMapVolumeSource(configMount.name))
      }

    val volumesSecrets =
      interaction.spec.secretMounts.map { configMount =>
        Volume(configMount.name, Volume.Secret(configMount.name))
      }

    val podSpec = Pod.Spec(
      containers = List(interactionContainerWithMounts1),
      volumes = volumesConfigMaps ++ volumesSecrets,
    )

    val podTemplate = Pod.Template.Spec
      .named(name)
      .withPodSpec(podSpec)
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
