package com.ing.bakery.clustercontroller.controllers

import cats.effect.{ContextShift, IO, Timer}
import com.ing.bakery.clustercontroller.MutualAuthKeystoreConfig
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.LabelSelector.IsEqualRequirement
import skuber.Volume.{ConfigMapProjection, ProjectedVolumeSource, SecretProjection}
import skuber.api.client.KubernetesClient
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{ConfigMap, Container, LabelSelector, LocalObjectReference, ObjectMeta, Pod, PodList, Protocol, Resource, Service, Volume}
import Utils.ConfigurableContainer

final class BakerController(interactionClientTLS: Option[MutualAuthKeystoreConfig] = None)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[BakerResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]

  def create(resource: BakerResource, k8s: KubernetesClient): IO[Unit] = {
    val cm = intermediateRecipesManifestConfigMap(resource)
    val dep = deployment(resource)
    val svc = service(resource)
    for {
      wasAlreadyThere1 <- idem(io(k8s.create[ConfigMap](cm)), s"recipes config map '${cm.name}'")
      wasAlreadyThere2 <- idem(attemptOpOrTryOlderVersion(
        v1 = io(k8s.create[Deployment](dep)).void,
        older = io(k8s.create[skuber.ext.Deployment](oldKubernetesDeployment(resource))).void), s"deployment '${dep.name}'")
      wasAlreadyThere3 <- idem(io(k8s.create(svc)), s"service '${svc.name}'")
    } yield {
      if(wasAlreadyThere1 || wasAlreadyThere2 || wasAlreadyThere3)
        logger.debug(s"Created (idem) baker cluster named '${resource.name}'")
      else
        logger.info(s"Created baker cluster named '${resource.name}'")
    }
  }

  def terminate(resource: BakerResource, k8s: KubernetesClient): IO[Unit] =
    for {
      _ <- io(k8s.delete[ConfigMap](intermediateRecipesManifestConfigMapName(resource)))
      (key, value) = recipeNameLabel(resource)
      _ <- io(k8s.delete[Service](service(resource).name))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](deployment(resource).name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldKubernetesDeployment(resource).name)))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void,
        older = io(k8s.deleteAllSelected[skuber.ext.ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void)
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ = logger.info(s"Terminated baker cluster named '${resource.name}'")
    } yield ()

  def upgrade(resource: BakerResource, k8s: KubernetesClient): IO[Unit] =
    for {
      _ <- io(k8s.update[ConfigMap](intermediateRecipesManifestConfigMap(resource))).void
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.update[Deployment](deployment(resource))).void,
        older = io(k8s.update[skuber.ext.Deployment](oldKubernetesDeployment(resource))).void)
      _ = logger.info(s"Upgraded baker cluster named '${resource.name}'")
    } yield ()

  private def recipeNodeLabel: (String, String) = "bakery-component" -> "baker"

  private def recipeNameLabel(resource: BakerResource): (String, String) = "bakery-baker-name" -> resource.name

  private def akkaClusterLabel(resource: BakerResource): (String, String) = "akka-cluster" -> resource.name

  private def intermediateRecipesManifestConfigMapName(resource: BakerResource): String = resource.name + "-manifest"

  private def recipeManifestLabel: (String, String) = "bakery-manifest" -> "recipes"

  private def baasStateServicePort: Int = 8081

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
          name = "app-metrics",
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
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")
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
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")
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
      .addLabel(recipeNodeLabel)
      .addLabel(recipeNameLabel(bakerResource))
      .addLabel(akkaClusterLabel(bakerResource))
  }

  private def deployment(bakerResource: BakerResource): Deployment = {

    val bakerCrdName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = recipeNameLabel(bakerResource)
    val replicas: Int = bakerResource.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = bakerCrdName,
      labels = Map(recipeNodeLabel, bakerLabelWithName) ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")))
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
      labels = Map(recipeNodeLabel, bakerLabelWithName) ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = bakerLabelWithName._1, value = bakerLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(bakerResource))
  }

  def service(bakerResource: BakerResource): Service = {
    val bakerCrdName: String = bakerResource.metadata.name
    Service(bakerCrdName)
      .addLabel(recipeNodeLabel)
      .addLabel(recipeNameLabel(bakerResource))
      .addLabel("metrics" -> "collect")
      .withSelector(recipeNameLabel(bakerResource))
      .setPorts(List(
        Some(Service.Port(
          name = "http-api",
          port = baasStateServicePort,
          targetPort = Some(Right("http-api"))
        )),
        Some(Service.Port(
          name = "app-metrics",
          port = 9095,
          targetPort = Some(Right("app-metrics"))
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
          recipeNodeLabel,
          recipeNameLabel(bakerResource),
          recipeManifestLabel
        )),
      data = bakerResource.recipes.get.map {
        case (serializedRecipe, compiledRecipe) => compiledRecipe.recipeId -> serializedRecipe
      }.toMap)
  }
}
