package com.ing.bakery.clustercontroller.controllers

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.clustercontroller.MutualAuthKeystoreConfig
import com.typesafe.scalalogging.LazyLogging
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
import ControllerOperations._

object BakerController {

  def run(
    configWatch: ForceRollingUpdateOnConfigMapUpdate, 
    interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
  )(implicit actorSystem: ActorSystem, 
    cs: ContextShift[IO], 
    timer: Timer[IO], 
    k8s: KubernetesClient
  ): Resource[IO, Unit] =
    new BakerController(configWatch, interactionClientTLS).runController()

  def runFromConfigMaps(
    configWatch: ForceRollingUpdateOnConfigMapUpdate, 
    interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
  )(implicit actorSystem: ActorSystem, 
    cs: ContextShift[IO], 
    timer: Timer[IO], 
    k8s: KubernetesClient
  ): Resource[IO, Unit] =
    new BakerController(configWatch, interactionClientTLS)
      .fromConfigMaps(BakerResource.fromConfigMap)
      .runController(labelFilter = Some("custom-resource-definition" -> "bakers"))
}

final class BakerController(
  configWatch: ForceRollingUpdateOnConfigMapUpdate, 
  interactionClientTLS: Option[MutualAuthKeystoreConfig] = None
)(implicit 
  cs: ContextShift[IO], 
  timer: Timer[IO]
) extends ControllerOperations[BakerResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]

  def create(resource: BakerResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    val createManifest: IO[Boolean] =
      idemCreate(intermediateRecipesManifestConfigMap(resource))

    val watchForManifestChangesToTriggerRollUpdate: IO[Unit] =
      configWatch.watchConfigOf(intermediateRecipesManifestConfigMapName(resource), deploymentName = resource.name)

    val createDeployment: IO[Boolean] =
      attemptOpOrTryOlderVersion(
        v1 = idemCreate(deployment(resource)),
        older = idemCreate(oldKubernetesDeployment(resource))
      ).map(_.fold(identity, identity))

    val watchForConfigChangesToTriggerRollUpdate: IO[Unit] =
      resource.spec.config.fold(IO.unit)(configWatch.watchConfigOf(_, deploymentName = resource.name))

    val createService: IO[Boolean] =
      idemCreate(service(resource))

    def logOutcome(manifestAlreadyExisted: Boolean, deploymentAlreadyExisted: Boolean, serviceAlreadyExisted: Boolean): IO[Unit] = IO {
      if (manifestAlreadyExisted || deploymentAlreadyExisted || serviceAlreadyExisted)
        logger.debug(s"Created (idem) baker cluster named '${resource.name}'")
      else
        logger.info(s"Created baker cluster named '${resource.name}'")
    }

    for {
      manifestAlreadyExisted <- createManifest
      deploymentAlreadyExisted <- createDeployment
      _ <- watchForManifestChangesToTriggerRollUpdate
      _ <- watchForConfigChangesToTriggerRollUpdate
      serviceAlreadyExisted <- createService
      _ <- logOutcome(manifestAlreadyExisted, deploymentAlreadyExisted, serviceAlreadyExisted)
    } yield ()
  }

  def terminate(resource: BakerResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    val manifestName: String =
      intermediateRecipesManifestConfigMapName(resource)

    val stopWatchingForManifestUpdates: IO[Unit] =
      configWatch.stopWatchingConfigOf(configMapName = manifestName, deploymentName = resource.name)

    val deleteManifest: IO[Unit] =
      io(k8s.delete[ConfigMap](manifestName))

    val deleteService: IO[Unit] =
      io(k8s.delete[Service](service(resource).name))

    val stopWatchingForDeploymentConfiguration =
      resource.spec.config.fold(IO.unit)(configWatch.stopWatchingConfigOf(_, deploymentName = resource.name))

    val deleteDeployment: IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](resource.name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldKubernetesDeployment(resource).name))
      ).void

    def deleteReplicaSet(labelKey: String, labelValue: String): IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(labelKey, labelValue)))).void,
        older = io(k8s.deleteAllSelected[skuber.ext.ReplicaSetList](LabelSelector(IsEqualRequirement(labelKey, labelValue)))).void
      ).void

    def deletePods(labelKey: String, labelValue: String): IO[Unit] =
      io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(labelKey, labelValue)))).void

    for {
      _ <- stopWatchingForManifestUpdates
      _ <- deleteManifest
      (labelKey, labelValue) = recipeNameLabel(resource)
      _ <- deleteService
      _ <- stopWatchingForDeploymentConfiguration
      _ <- deleteDeployment
      _ <- deleteReplicaSet(labelKey, labelValue)
      _ <- deletePods(labelKey, labelValue)
      _ = logger.info(s"Terminated baker cluster named '${resource.name}'")
    } yield ()
  }

  def upgrade(resource: BakerResource)(implicit k8s: KubernetesClient): IO[Unit] = {

    val updateManifest: IO[Unit] =
      io(k8s.update[ConfigMap](intermediateRecipesManifestConfigMap(resource))).void

    val updateDeployment: IO[Unit] =
      attemptOpOrTryOlderVersion(
        v1 = io(k8s.update[Deployment](deployment(resource))).void,
        older = io(k8s.update[skuber.ext.Deployment](oldKubernetesDeployment(resource))).void
      ).void

    val updateConfigWatch: IO[Unit] =
      resource.spec.config match {
        case None =>
          configWatch.stopWatchingConfigFor(resource.name)
        case Some(newConfig) =>
          configWatch.stopWatchingConfigFor(resource.name) *> configWatch.watchConfigOf(newConfig, resource.name)
      }

    for {
      _ <- updateManifest
      _ <- updateDeployment
      /* When updating a BakerResource at this point we don't know if the config was added, removed, or left
       * untouched, that is why we ensure that if the config is not in the resource, then it is removed from cache,
       * and if the config was updated the old deployment entry is removed and the new one added
       */
      _ <- updateConfigWatch
      _ = logger.info(s"Upgraded baker cluster named '${resource.name}'")
    } yield ()
  }

  /** Used to identify Kubernetes resources that belong to Baker nodes. */
  private def bakeryBakerLabel: (String, String) = "bakery-component" -> "baker"

  /** Used to identify Kubernetes resources that belong to this specific Baker node. */
  private def recipeNameLabel(resource: BakerResource): (String, String) = "bakery-baker-name" -> resource.name

  /** Used for the Akka Cluster Kubernetes service discovery to form an Akka Cluster. */
  private def akkaClusterLabel(resource: BakerResource): (String, String) = "akka-cluster" -> resource.name

  /** Name of the ConfigMap that contains the node recipes to be mounted in the Baker node Pods. */
  private def intermediateRecipesManifestConfigMapName(resource: BakerResource): String = resource.name + "-manifest"

  /** Used to identify the ConfigMaps that are Baker manifests. */
  private def recipeManifestLabel: (String, String) = "bakery-manifest" -> "recipes"

  /** Default port to be used for the Baker node http server. */
  private def bakeryBakerServicePort: Int = 8081

  private def podSpec(bakerResource: BakerResource): Pod.Template.Spec = {

    val bakerCrdName: String = bakerResource.metadata.name
    val image: String = bakerResource.spec.image
    val imagePullSecret: Option[String] = bakerResource.spec.imagePullSecret
    val serviceAccountSecret: Option[String] = bakerResource.spec.serviceAccountSecret
    val recipesMountPath: String = "/recipes"
    val managementPort = Container.Port(
      name = "management",
      containerPort = 8558,
      protocol = Protocol.TCP
    )

    val stateNodeContainer = Container(
        name = bakerCrdName,
        image = image
      )
        .exposePort(Container.Port(
          name = "remoting",
          containerPort = 2552,
          protocol = Protocol.TCP
        ))
        .exposePort(managementPort)
        .exposePort(Container.Port(
          name = "prometheus",
          containerPort = 9095,
          protocol = Protocol.TCP
        ))
        .applyIfNotDefined(bakerResource.spec.sidecar, _.exposePort(Container.Port(
          name = "http-api",
          containerPort = 8080,
          protocol = Protocol.TCP
        )))
        .withReadinessProbe(skuber.Probe(
          action = skuber.HTTPGetAction(
            port = Right(managementPort.name),
            path = "/health/ready"
          ),
          initialDelaySeconds = 15,
          timeoutSeconds = 10,
          failureThreshold = Some(30)
        ))
        .withLivenessProbe(skuber.Probe(
          action = skuber.HTTPGetAction(
            port = Right(managementPort.name),
            path = "/health/alive"
          ),
          initialDelaySeconds = 15,
          timeoutSeconds = 10,
          failureThreshold = Some(30)
        ))
        .mount("recipes", recipesMountPath, readOnly = true)
        .mount("config", "/bakery-config", readOnly = true)
        .applyIfDefined(serviceAccountSecret, (_: String, c) => c.mount(name = "service-account-token", "/var/run/secrets/kubernetes.io/serviceaccount", readOnly = true))
        .setEnvVar("STATE_CLUSTER_SELECTOR", bakerCrdName)
        .setEnvVar("RECIPE_DIRECTORY", recipesMountPath)
        .setEnvVar("BAKERY_SCOPE", bakerResource.metadata.labels.getOrElse("scope", "*"))
        .setEnvVar("API_LOGGING_ENABLED", bakerResource.spec.apiLoggingEnabled.toString)
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:MaxRAMPercentage=85.0")
        .maybeWithKeyStoreConfig("INTERACTION_CLIENT", interactionClientTLS)
        .withMaybeResources(bakerResource.spec.resources)
        .withMaybeKafkaSink(bakerResource.spec.kafkaBootstrapServers)

    val maybeSidecarContainer: Option[Container] = bakerResource.spec.sidecar map { sidecarSpec => Container(
        name = bakerCrdName + "-sidecar",
        image = sidecarSpec.image
      )
        .exposePort(Container.Port(
          name = "http-api",
          containerPort = 8443,
          protocol = Protocol.TCP
        ))
        .exposePort(Container.Port(
          name = "sidecar-metrics",
          containerPort = 10080,
          protocol = Protocol.TCP
        ))
        .applyIfDefined(sidecarSpec.configVolumeMountPath, (v: String, c) => c.mount("config", v, readOnly = true))
        .applyIfDefined(sidecarSpec.environment, (e: Map[String, String], c) => c.withEnvironment(e))
        .withMaybeResources(sidecarSpec.resources)
        .applyIfDefined(sidecarSpec.livenessProbe, (p: skuber.Probe, c) => c.withLivenessProbe(p))
        .applyIfDefined(sidecarSpec.readinessProbe, (p: skuber.Probe, c) => c.withReadinessProbe(p))
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:MaxRAMPercentage=85.0")
    }

    val podSpec = Pod.Spec(
      containers = List(Some(stateNodeContainer), maybeSidecarContainer).flatten,
      imagePullSecrets = imagePullSecret.map(s => List(LocalObjectReference(s))).getOrElse(List.empty),
      volumes = List(
        serviceAccountSecret.map(s => Volume("service-account-token", Volume.Secret(s))),
        Some(Volume(
          name = "recipes",
          source = Volume.ConfigMapVolumeSource(intermediateRecipesManifestConfigMapName(bakerResource)))),
        Some(Volume(
          name = "config",
          source = ProjectedVolumeSource(
            sources = List(
              Some(ConfigMapProjection(intermediateRecipesManifestConfigMapName(bakerResource))),
              bakerResource.spec.config.map(ConfigMapProjection(_)),
              bakerResource.spec.secrets.map(SecretProjection(_)),
              interactionClientTLS.map(c => SecretProjection(c.secretName))
            ).flatten)))
    ).flatten)

    Pod.Template.Spec
      .named(bakerCrdName)
      .withPodSpec(podSpec)
      .addLabels(bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition"))
      .addLabel(bakeryBakerLabel)
      .addLabel(recipeNameLabel(bakerResource))
      .addLabel(akkaClusterLabel(bakerResource))
      .addLabel(ForceRollingUpdateOnConfigMapUpdate.componentForceUpdateLabel)
  }

  private def deployment(bakerResource: BakerResource): Deployment = {

    val bakerCrdName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = recipeNameLabel(bakerResource)
    val replicas: Int = bakerResource.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = bakerCrdName,
      labels = Map(
        "app" -> bakerCrdName,
        bakeryBakerLabel,
        bakerLabelWithName)
        ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = bakerLabelWithName._1, value = bakerLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(bakerResource))
  }

  private def oldKubernetesDeployment(bakerResource: BakerResource): skuber.ext.Deployment = {

    val bakerCrdName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = recipeNameLabel(bakerResource)
    val replicas: Int = bakerResource.spec.replicas

    new skuber.ext.Deployment(metadata = ObjectMeta(
      name = bakerCrdName,
      labels = Map(
        "app" -> bakerCrdName,
        bakeryBakerLabel,
        bakerLabelWithName)
        ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = bakerLabelWithName._1, value = bakerLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(bakerResource))
  }

  def service(bakerResource: BakerResource): Service = {
    val bakerCrdName: String = bakerResource.metadata.name
    Service(bakerCrdName)
      .addLabel(bakeryBakerLabel)
      .addLabel(recipeNameLabel(bakerResource))
      .addLabels(bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition"))
      .addLabel("metrics" -> "collect")
      .withSelector(recipeNameLabel(bakerResource))
      .setPorts(List(
        Some(Service.Port(
          name = "http-api",
          port = bakeryBakerServicePort,
          targetPort = Some(Right("http-api"))
        )),
        Some(Service.Port(
          name = "prometheus",
          port = 9095,
          targetPort = Some(Right("prometheus"))
        )),
        bakerResource.spec.sidecar.map(_ =>
          Service.Port(
            name = "sidecar-metrics",
            port = 10080,
            targetPort = Some(Right("sidecar-metrics"))
          ))
      ).flatten)
  }

  private def intermediateRecipesManifestConfigMap(bakerResource: BakerResource): ConfigMap = {
    new ConfigMap(
      metadata = ObjectMeta(
        name = intermediateRecipesManifestConfigMapName(bakerResource),
        labels = Map(
          bakeryBakerLabel,
          recipeNameLabel(bakerResource),
          recipeManifestLabel,
          ForceRollingUpdateOnConfigMapUpdate.componentConfigWatchLabel
        ) ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")),
      data = bakerResource.recipes.get.map {
        case (serializedRecipe, compiledRecipe) => compiledRecipe.recipeId -> serializedRecipe
      }.toMap)
  }
}
