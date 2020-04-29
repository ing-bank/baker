package com.ing.bakery.clustercontroller.controllers

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.baker.baas.interaction.RemoteInteractionClient.InteractionEndpoint
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.ext.{Deployment, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{ConfigMap, Container, LabelSelector, LocalObjectReference, ObjectMeta, Pod, PodList, Protocol, Service, Volume}

import scala.concurrent.Future
import scala.concurrent.duration._

final class InteractionController(httpClient: Client[IO])(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[InteractionResource] with LazyLogging {

  // TODO make these operations atomic, if one fails we need to rollback previous ones
  def create(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] = {
    val address = Uri.unsafeFromString(s"http://${serviceName(resource)}:${httpAPIPort.containerPort}/")
    val client = new RemoteInteractionClient(httpClient, address)
    for {
      _ <- io(k8s.create(deployment(resource)))
      _ <- io(k8s.create(service(resource)))
      interfaces <- Utils.within(10.minutes, split = 300) { // Check every 2 seconds for interfaces
        client.interface.map { interfaces =>assert(interfaces.nonEmpty); interfaces }
      }
      _ <- io(k8s.create(creationContract(resource, address, interfaces)))
      _ = logger.info(s"Deployed interactions from interaction set named '${resource.name}': ${interfaces.map(_.name).mkString(", ")}")
    } yield ()
  }

  def terminate(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] = {
    val (key, value) = interactionLabel(resource)
    for {
      _ <- io(k8s.delete[ConfigMap](creationContractName(resource)))
      _ <- io(k8s.delete[Service](serviceName(resource)))
      _ <- io(k8s.delete[Deployment](deploymentName(resource)))
      _ <- io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ = logger.info(s"Terminated interaction set named '${resource.name}'")
    } yield ()
  }

  def upgrade(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] =
    for {
      _ <- io(k8s.update[skuber.ext.Deployment](deployment(resource)))
    } yield ()

  private def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))

  private def interactionLabel(interaction: InteractionResource): (String, String) = "interaction" -> interaction.name

  private def serviceName(interactionResource: InteractionResource): String = interactionResource.name + "-interaction-service"

  private def deploymentName(interactionResource: InteractionResource): String = interactionResource.name

  private def creationContractName(interactionResource: InteractionResource): String = "interactions-" + interactionResource.name

  private def baasComponentLabel: (String, String) = "baas-component" -> "remote-interaction-interfaces"

  private def httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  private def creationContract(interaction: InteractionResource, address: Uri, interactions: List[InteractionEndpoint]): ConfigMap = {
    val name = creationContractName(interaction)
    val interactionsData = InteractionEndpoint.toBase64(interactions)
    ConfigMap(
      metadata = ObjectMeta(name = name, labels = Map(baasComponentLabel)),
      data = Map("address" -> address.toString, "interfaces" -> interactionsData)
    )
  }

  private def deployment(interaction: InteractionResource): Deployment = {

    val name: String = deploymentName(interaction)
    val image: String = interaction.spec.image
    val imagePullSecret: Option[String] = interaction.spec.imagePullSecret
    val replicas: Int = interaction.spec.replicas

    val healthProbe = skuber.Probe(
      action = skuber.HTTPGetAction(
        port = Right(httpAPIPort.name),
        path = "/api/v3/health"
      ),
      initialDelaySeconds = 15,
      timeoutSeconds = 10
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
      imagePullSecrets = imagePullSecret.map(s => List(LocalObjectReference(s))).getOrElse(List.empty),
      volumes = volumesConfigMaps ++ volumesSecrets,
    )

    val podTemplate = Pod.Template.Spec
      .named(name)
      .withPodSpec(podSpec)
      .addLabel(interactionLabel(interaction))

    new Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(
        interactionLabel(interaction),
        ("app", interaction.name))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  private def service(interaction: InteractionResource): Service = {
    Service(serviceName(interaction))
      .withSelector(interactionLabel(interaction))
      .addLabel("app", interaction.name)
      .setPort(Service.Port(
        name = httpAPIPort.name,
        port = httpAPIPort.containerPort
      ))
  }
}
