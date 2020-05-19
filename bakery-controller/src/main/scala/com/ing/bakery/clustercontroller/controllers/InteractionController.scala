package com.ing.bakery.clustercontroller.controllers

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.baker.baas.interaction.RemoteInteractionClient.InteractionEndpoint
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import play.api.libs.json.Format
import skuber.K8SException
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.json.format._
import skuber.json.ext.format._
import skuber.{ConfigMap, Container, LabelSelector, LocalObjectReference, ObjectMeta, Pod, PodList, Protocol, Service, Volume}

import scala.concurrent.Future
import scala.concurrent.duration._

final class InteractionController(httpClient: Client[IO])(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[InteractionResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]

  // TODO make these operations atomic, if one fails we need to rollback previous ones
  def create(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] = {
    for {
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.create[Deployment](deployment(resource))).void,
        older = io(k8s.create[skuber.ext.Deployment](oldDeployment(resource))).void)
      deployedService <- io(k8s.create(service(resource)))
      deployedPort = deployedService.spec
        .flatMap(_.ports.find(_.name == "http-api"))
        .map(_.port)
        .getOrElse(8080)
      address = Uri.unsafeFromString(s"http://${serviceName(resource)}:$deployedPort/")
      client = new RemoteInteractionClient(httpClient, address)
      interfaces <- Utils.within(10.minutes, split = 300) { // Check every 2 seconds for interfaces
        client.interface.map { interfaces => assert(interfaces.nonEmpty); interfaces }
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
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](deployment(resource).name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldDeployment(resource).name)))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void,
        older = io(k8s.deleteAllSelected[skuber.ext.ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void)
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ = logger.info(s"Terminated interaction set named '${resource.name}'")
    } yield ()
  }

  def upgrade(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] =
    for {
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.update[Deployment](deployment(resource))).void,
        older = io(k8s.update[skuber.ext.Deployment](oldDeployment(resource))).void)
    } yield ()

  /**
    * This attempts to make a skuber operation (normaly an api call to api version apps/v1), if the error is 404,
    * that means we are in an old kubernetes environment and we need to use an older version like extensions/apps/v1beta1
    */
  private def attemptOpOrTryOlderVersion(v1: IO[Unit], older: IO[Unit]): IO[Unit] =
    v1.attempt.flatMap {
      case Left(e: K8SException) if e.status.code.contains(404) => older
      case Left(e) => IO.raiseError(e)
      case Right(a) => IO.pure(a)
    }

  private def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))

  private def interactionLabel(interaction: InteractionResource): (String, String) = "interaction" -> interaction.name

  private def serviceName(interactionResource: InteractionResource): String = interactionResource.name

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

  private def podSpec(interaction: InteractionResource): Pod.Template.Spec = {

    val name: String = deploymentName(interaction)
    val interactionLabelWithName: (String, String) = interactionLabel(interaction)
    val image: String = interaction.spec.image
    val imagePullSecret: Option[String] = interaction.spec.imagePullSecret

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

    Pod.Template.Spec
      .named(name)
      .withPodSpec(podSpec)
      .addLabel(interactionLabelWithName)
  }

  private def deployment(interaction: InteractionResource): Deployment = {

    val name: String = deploymentName(interaction)
    val interactionLabelWithName: (String, String) = interactionLabel(interaction)
    val replicas: Int = interaction.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(
        interactionLabelWithName,
        ("app", interaction.name))
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = interactionLabelWithName._1, value = interactionLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(interaction))
  }

  private def oldDeployment(interaction: InteractionResource): skuber.ext.Deployment = {

    val name: String = deploymentName(interaction)
    val interactionLabelWithName: (String, String) = interactionLabel(interaction)
    val replicas: Int = interaction.spec.replicas

    new skuber.ext.Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(
        interactionLabelWithName,
        ("app", interaction.name))
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = interactionLabelWithName._1, value = interactionLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(interaction))
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
