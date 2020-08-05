package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.bakery.clustercontroller.MutualAuthKeystoreConfig
import com.ing.baker.baas.protocol.{InteractionExecution => I}
import com.typesafe.scalalogging.LazyLogging
import io.circe.syntax._
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder
import play.api.libs.json.Format
import skuber.LabelSelector.IsEqualRequirement
import skuber.Volume.{ConfigMapProjection, ProjectedVolumeSource, SecretProjection}
import skuber.api.client.KubernetesClient
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{ConfigMap, Container, LabelSelector, LocalObjectReference, ObjectMeta, Pod, PodList, Protocol, Service, Volume}
import Utils.ConfigurableContainer


import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

final class InteractionController(connectionPool: ExecutionContext, interactionTLS: Option[MutualAuthKeystoreConfig] = None, interactionClientTLS: Option[MutualAuthKeystoreConfig] = None)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[InteractionResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]
  import com.ing.baker.baas.protocol.InteractionExecutionJsonCodecs._

  // TODO make these operations atomic, if one fails we need to rollback previous ones
  def create(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] = {
    val dpl = deployment(resource)
    val svc = service(resource)
    for {
      wasAlreadyThere1 <- idem(attemptOpOrTryOlderVersion(
        v1 = io(k8s.create[Deployment](dpl)).void,
        older = io(k8s.create[skuber.ext.Deployment](oldKubernetesDeployment(resource))).void), s"deployment '${dpl.name}'")
      deployedService <- applyOrGet(io(k8s.create(svc)), io(k8s.get[Service](svc.name)), s"service '${svc.name}'")
      deployedPort = deployedService.spec
        .flatMap(_.ports.find(_.name == "http-api"))
        .map(_.port)
        .getOrElse(8080)
      addressAndInterfaces <- extractInterfacesFromDeployedInteraction(resource.name, deployedPort, k8s)
      (address, interfaces) = addressAndInterfaces
      contract = creationContract(resource, address, interfaces)
      wasAlreadyThere2 <- idem(io(k8s.create(contract)), s"creation contract config map '${contract.name}'")
    } yield {
      if(wasAlreadyThere1 || wasAlreadyThere2)
        logger.debug(s"Deployed (idem) interactions from interaction set named '${resource.name}': ${interfaces.map(_.name).mkString(", ")}")
      else
        logger.info(s"Deployed interactions from interaction set named '${resource.name}': ${interfaces.map(_.name).mkString(", ")}")
    }
  }

  def terminate(resource: InteractionResource, k8s: KubernetesClient): IO[Unit] = {
    val (key, value) = interactionNameLabel(resource)
    for {
      _ <- io(k8s.delete[ConfigMap](intermediateInteractionWitnessConfigMapName(resource)))
      _ <- io(k8s.delete[Service](resource.name))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](deployment(resource).name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldKubernetesDeployment(resource).name)))
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
        older = io(k8s.update[skuber.ext.Deployment](oldKubernetesDeployment(resource))).void)
    } yield ()

  private def extractInterfacesFromDeployedInteraction(serviceName: String, deployedPort: Int, k8s: KubernetesClient): IO[(Uri, List[I.Interaction])] = {
    val protocol = if(interactionClientTLS.isDefined) "https" else "http"
    val address = Uri.unsafeFromString(s"$protocol://$serviceName:$deployedPort/")
    for {
      tlsConfig <- interactionClientTLS.traverse(_.loadKeystore(k8s))
      interfaces <- BlazeClientBuilder[IO](connectionPool, tlsConfig)
        .withCheckEndpointAuthentication(false)
        .resource.use { client =>
          val interactionClient = new RemoteInteractionClient(client, address)
          Utils.within(10.minutes, split = 300) { // Check every 2 seconds for interfaces
            interactionClient.interface.map { interfaces => assert(interfaces.nonEmpty); interfaces }
          }
        }
    } yield (address, interfaces)
  }

  private def interactionNodeLabel: (String, String) = "bakery-component" -> "interaction-node"

  private def interactionNameLabel(interaction: InteractionResource): (String, String) = "bakery-interaction-name" -> interaction.name

  private def intermediateInteractionWitnessConfigMapName(interaction: InteractionResource): String = interaction.name + "-witness"

  private def interactionWitnessLabel: (String, String) = "bakery-witness" -> "interactions"

  private def httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  import com.ing.baker.baas.protocol.InteractionExecutionJsonCodecs._


  private def creationContract(interaction: InteractionResource, address: Uri, interactions: List[I.Interaction]): ConfigMap = {
    val name = intermediateInteractionWitnessConfigMapName(interaction)
    val interactionsData =  interactions.asJson.toString
    ConfigMap(
      metadata = ObjectMeta(name = name, labels = Map(
        interactionNodeLabel,
        interactionNameLabel(interaction),
        interactionWitnessLabel
      )),
      data = Map("address" -> address.toString, "interfaces" -> interactionsData)
    )
  }

  private def podSpec(interaction: InteractionResource): Pod.Template.Spec = {

    val image: String = interaction.spec.image
    val imagePullSecret: Option[String] = interaction.spec.imagePullSecret

    val healthProbe = skuber.Probe(
      action = skuber.HTTPGetAction(
        port = Left(9999),
        path = "/health"
      ),
      initialDelaySeconds = 15,
      timeoutSeconds = 10
    )

    val interactionContainer = Container(
      name = interaction.name,
      image = image)
      .exposePort(httpAPIPort)
      .exposePort(Container.Port(
        name = "prometheus",
        containerPort = 9095,
        protocol = Protocol.TCP
      ))
      .exposePort(Container.Port(
        name = "health",
        containerPort = 9999,
        protocol = Protocol.TCP
      ))
      .withReadinessProbe(healthProbe.copy(failureThreshold = Some(30)))
      .withLivenessProbe(healthProbe.copy(failureThreshold = Some(30)))
      .copy(env = interaction.spec.env)
      .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")
      .maybeWithKeyStoreConfig("INTERACTION", interactionTLS)
      .withMaybeResources(interaction.spec.resources)
      .mount("config", "/bakery-config", readOnly = true)

    val podSpec = Pod.Spec(
      containers = List(interactionContainer),
      imagePullSecrets = imagePullSecret.map(s => List(LocalObjectReference(s))).getOrElse(List.empty),
      volumes = List(
        Volume(name = "config",
          source = ProjectedVolumeSource(
            sources = (interaction.spec.configMapMounts.getOrElse(List.empty).map(m => Some(ConfigMapProjection(m))) ++
              interaction.spec.secretMounts.getOrElse(List.empty).map(m => Some(SecretProjection(m))) ++
              List(interactionTLS.map(c => SecretProjection(c.secretName)))).flatten)
        )
      )
    )

    Pod.Template.Spec
      .named(interaction.name)
      .withPodSpec(podSpec)
      .addLabel(interactionNodeLabel)
      .addLabel(interactionNameLabel(interaction))
  }

  private def deployment(interaction: InteractionResource): Deployment = {

    val interactionLabelWithName: (String, String) = interactionNameLabel(interaction)
    val replicas: Int = interaction.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = interaction.name,
      labels = Map(
        interactionNodeLabel,
        interactionNameLabel(interaction)) ++
        interaction.metadata.labels.filter(_._1 != "custom-resource-definition")
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = interactionLabelWithName._1, value = interactionLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(interaction))
  }

  private def oldKubernetesDeployment(interaction: InteractionResource): skuber.ext.Deployment = {

    val interactionLabelWithName: (String, String) = interactionNameLabel(interaction)
    val replicas: Int = interaction.spec.replicas

    new skuber.ext.Deployment(metadata = ObjectMeta(
      name = interaction.name,
      labels = Map(
        interactionNodeLabel,
        interactionNameLabel(interaction)) ++
        interaction.metadata.labels.filter(_._1 != "custom-resource-definition")
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = interactionLabelWithName._1, value = interactionLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(interaction))
  }

  private def service(interaction: InteractionResource): Service = {
    Service(interaction.name)
      .addLabel(interactionNodeLabel)
      .addLabel(interactionNameLabel(interaction))
      .addLabel("metrics" -> "collect")
      .withSelector(interactionNameLabel(interaction))
      .setPorts(List(
        Service.Port(
          name = httpAPIPort.name,
          port = httpAPIPort.containerPort
        ),
        Service.Port(
          name = "prometheus",
          port = 9095,
          targetPort = Some(Right("prometheus"))
        )
      ))
  }
}
