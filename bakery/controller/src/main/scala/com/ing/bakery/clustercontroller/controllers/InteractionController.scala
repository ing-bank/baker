package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.clustercontroller.MutualAuthKeystoreConfig
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
import akka.actor.ActorSystem
import com.ing.bakery.interaction.RemoteInteractionClient
import ControllerOperations._
import com.ing.baker.runtime.serialization.InteractionExecution

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

object InteractionController {

  def run(
    configWatch: ForceRollingUpdateOnConfigMapUpdate, 
    connectionPool: ExecutionContext, 
    interactionTLS: Option[MutualAuthKeystoreConfig] = None, 
    interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
  )(implicit 
    actorSystem: ActorSystem, 
    k8s: KubernetesClient, 
    cs: ContextShift[IO], 
    timer: Timer[IO]
  ): Resource[IO, Unit] =
    new InteractionController(configWatch, connectionPool, interactionTLS, interactionClientTLS).runController()

  def runFromConfigMaps(
    configWatch: ForceRollingUpdateOnConfigMapUpdate,
    connectionPool: ExecutionContext,
    interactionTLS: Option[MutualAuthKeystoreConfig] = None,
    interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
  )(implicit 
    actorSystem: ActorSystem,
    k8s: KubernetesClient,
    cs: ContextShift[IO],
    timer: Timer[IO]
  ): Resource[IO, Unit] =
    new InteractionController(configWatch, connectionPool, interactionTLS, interactionClientTLS)
      .fromConfigMaps(InteractionResource.fromConfigMap)
      .runController(labelFilter = Some("custom-resource-definition" -> "interactions"))
}

final class InteractionController(
  configWatch: ForceRollingUpdateOnConfigMapUpdate, 
  connectionPool: ExecutionContext, 
  interactionTLS: Option[MutualAuthKeystoreConfig] = None, 
  interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
)(implicit 
  cs: ContextShift[IO], 
  timer: Timer[IO]
) extends ControllerOperations[InteractionResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]
  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._

  // TODO make these operations atomic, if one fails we need to rollback previous ones
  def create(resource: InteractionResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    val createDeployment: IO[Boolean] =
      attemptOpOrTryOlderVersion(
        v1 = idemCreate(deployment(resource)),
        older = idemCreate(oldKubernetesDeployment(resource))
      ).map(_.fold(identity, identity))

    def logOutcome(deploymentAlreadyExisted: Boolean, manifestAlreadyExisted: Boolean, interfaces: List[InteractionExecution.Descriptor]): IO[Unit] = IO {
      if(deploymentAlreadyExisted || manifestAlreadyExisted)
        logger.debug(s"Deployed (idem) interactions from interaction set named '${resource.name}': ${interfaces.map(_.name).mkString(", ")}")
      else
        logger.info(s"Deployed interactions from interaction set named '${resource.name}': ${interfaces.map(_.name).mkString(", ")}")
    }

    for {
      deploymentAlreadyExisted <- createDeployment
      _ <- watchForConfigChangesToTriggerRollUpdate(resource)
      deployedService <- createOrFetch(service(resource))
      addressAndInterfaces <- extractInterfacesFromDeployedInteraction(deployedService, k8s)
      (address, interfaces) = addressAndInterfaces
      manifestAlreadyExisted <- idemCreate(interactionManifest(resource, address, interfaces))
      _ <- logOutcome(deploymentAlreadyExisted, manifestAlreadyExisted, interfaces)
    } yield ()
  }

  def terminate(resource: InteractionResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    val (key, value) = interactionNameLabel(resource)

    val deleteDeployment: IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](deployment(resource).name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldKubernetesDeployment(resource).name))
      ).void

    val deleteReplicaSetList: IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void,
        older = io(k8s.deleteAllSelected[skuber.ext.ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void
      ).void

    val deletePodList: IO[Unit] =
      io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value)))).void

    for {
      _ <- io(k8s.delete[ConfigMap](intermediateInteractionManifestConfigMapName(resource)))
      _ <- io(k8s.delete[Service](resource.name))
      _ <- deleteDeployment
      _ <- stopWatchingForConfigMaps(resource)
      _ <- deleteReplicaSetList
      _ <- deletePodList
      _ = logger.info(s"Terminated interaction set named '${resource.name}'")
    } yield ()
  }

  def upgrade(resource: InteractionResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    def updateDeployment: IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.update[Deployment](deployment(resource))),
        older = io(k8s.update[skuber.ext.Deployment](oldKubernetesDeployment(resource)))).void

    def updateManifest(addressAndInterfaces: (Uri, List[InteractionExecution.Descriptor])): IO[Unit] = {
      val (address, interfaces) = addressAndInterfaces
      io(k8s.update[ConfigMap](interactionManifest(resource, address, interfaces))).void
    }

    for {
      _ <- updateDeployment
      /* When updating an InteractionResource at this point we don't know if the config was added, removed, or left
       * untouched, that is why we ensure that if the config is not in the resource, then it is removed from cache,
       * and if the config was updated the old deployment entry is removed and the new one added
       */
      deployedService <- createOrFetch(service(resource))
      addressAndInterfaces <- extractInterfacesFromDeployedInteraction(deployedService, k8s, versionCheck = Some(resource.spec.image))
      _ <- updateManifest(addressAndInterfaces)
      _ <- {
        if (resource.spec.configMapMounts.isDefined)
          configWatch.stopWatchingConfigFor(resource.name) *> watchForConfigChangesToTriggerRollUpdate(resource)
        else
          configWatch.stopWatchingConfigFor(resource.name)
      }
    } yield ()
  }

  private def forAllConfigMapMounts(resource: InteractionResource, f: String => IO[Unit]): IO[Unit] =
    resource.spec.configMapMounts.fold(IO.unit)(configMaps =>
      configMaps.parTraverse(f).runAsync {
        case Left(e) => IO(logger.error("Failed at configuring a watch on interaction config mounts", e))
        case Right(_) => IO.unit
      }.toIO)

  private def watchForConfigChangesToTriggerRollUpdate(interaction: InteractionResource)(implicit k8s: KubernetesClient): IO[Unit] =
    forAllConfigMapMounts(interaction, configWatch.watchConfigOf(_, interaction.name))

  private def stopWatchingForConfigMaps(interaction: InteractionResource)(implicit k8s: KubernetesClient): IO[Unit] =
    forAllConfigMapMounts(interaction, configWatch.stopWatchingConfigOf(_, interaction.name))

  private def extractInterfacesFromDeployedInteraction(deployedService: Service, k8s: KubernetesClient, versionCheck: Option[String] = None): IO[(Uri, List[InteractionExecution.Descriptor])] = {
    val deployedPort = deployedService.spec
      .flatMap(_.ports.find(_.name == "http-api"))
      .map(_.port)
      .getOrElse(8080)
    val protocol = if(interactionClientTLS.isDefined) "https" else "http"
    val address = Uri.unsafeFromString(s"$protocol://${deployedService.name}:$deployedPort/")

    def interfacesPoll(client: RemoteInteractionClient): IO[List[InteractionExecution.Descriptor]] =
      Utils.within(10.minutes, split = 300) { // Check every 2 seconds for interfaces for 10 minutes
        versionCheck match {
          case Some(vcheck) =>
            client.interface.map { result =>
              assert(result.nonEmpty)
              result
            }
          case None =>
            client.interface.map { interfaces => assert(interfaces.nonEmpty); interfaces }
        }
      }

    for {
      tlsConfig <- interactionClientTLS.traverse(_.loadKeystore(k8s))
      interfaces <- BlazeClientBuilder[IO](connectionPool, tlsConfig)
        .withCheckEndpointAuthentication(false)
        .resource.use { client =>
          interfacesPoll(new RemoteInteractionClient(client, address))
        }
    } yield (address, interfaces)
  }

  /** Used to identify Kubernetes resources that belong to Interaction nodes. */
  private def interactionNodeLabel: (String, String) = "bakery-component" -> "interaction"

  /** Used to identify Kubernetes resources that belong to this specific Interaction node. */
  private def interactionNameLabel(interaction: InteractionResource): (String, String) = "bakery-interaction-name" -> interaction.name

  /** Name for the manifest that publishes the interaction interfaces of this Interaction node. */
  private def intermediateInteractionManifestConfigMapName(interaction: InteractionResource): String = interaction.name + "-manifest"

  /** Used by the Baker nodes to discover the interfaces and locations of the interactions published by the Interaction nodes. */
  private def interactionManifestLabel: (String, String) = "bakery-manifest" -> "interactions"

  private def httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._


  private def interactionManifest(interaction: InteractionResource, address: Uri, interactions: List[InteractionExecution.Descriptor]): ConfigMap = {
    val name = intermediateInteractionManifestConfigMapName(interaction)
    val interactionsData =  interactions.asJson.toString
    ConfigMap(
      metadata = ObjectMeta(name = name, labels = Map(
        interactionNodeLabel,
        interactionNameLabel(interaction),
        interactionManifestLabel) ++
        interaction.metadata.labels.filter(_._1 != "custom-resource-definition")
      ),
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
      .withReadinessProbe(healthProbe.copy(failureThreshold = Some(30)))
      .withLivenessProbe(healthProbe.copy(failureThreshold = Some(30)))
      .copy(env = interaction.spec.env)
      .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:MaxRAMPercentage=85.0")
      .setEnvVar("BAKERY_INTERACTION_VERSION", interaction.spec.image)
      .maybeWithKeyStoreConfig("INTERACTION", interactionTLS)
      .withMaybeResources(interaction.spec.resources)
      .mount("config", "/bakery-config", readOnly = true)

    val podSpec = Pod.Spec(
      containers = List(interactionContainer),
      imagePullSecrets = imagePullSecret.map(s => List(LocalObjectReference(s))).getOrElse(List.empty),
      volumes =
        if (interaction.spec.configMapMounts.isEmpty && interaction.spec.secretMounts.isEmpty) List.empty
        else List(
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
      .addLabels(interaction.metadata.labels.filter(_._1 != "custom-resource-definition"))
  }

  private def deployment(interaction: InteractionResource): Deployment = {

    val interactionLabelWithName: (String, String) = interactionNameLabel(interaction)
    val replicas: Int = interaction.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = interaction.name,
      labels = Map(
        "app" -> interaction.metadata.name,
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
        "app" -> interaction.metadata.name,
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
      .addLabels(interaction.metadata.labels.filter(_._1 != "custom-resource-definition"))
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
