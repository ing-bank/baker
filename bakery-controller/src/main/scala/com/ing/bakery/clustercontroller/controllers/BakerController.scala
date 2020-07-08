package com.ing.bakery.clustercontroller.controllers

import cats.effect.{ContextShift, IO, Timer}
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{ConfigMap, Container, LabelSelector, LocalObjectReference, ObjectMeta, Pod, PodList, Protocol, Service, Volume}

final class BakerController(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[BakerResource] with LazyLogging {

  implicit lazy val replicaSetListFormat: Format[ReplicaSetList] = ListResourceFormat[ReplicaSet]

  def create(resource: BakerResource, k8s: KubernetesClient): IO[Unit] = {
    val cm = configMap(resource)
    val dep = deployment(resource)
    val svc = service(resource)
    for {
      wasAlreadyThere1 <- idem(io(k8s.create[ConfigMap](cm)), s"recipes config map '${cm.name}'")
      wasAlreadyThere2 <- idem(attemptOpOrTryOlderVersion(
        v1 = io(k8s.create[Deployment](dep)).void,
        older = io(k8s.create[skuber.ext.Deployment](oldDeployment(resource))).void), s"deployment '${dep.name}'")
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
      _ <- io(k8s.delete[ConfigMap](baasRecipesConfigMapName(resource.metadata.name)))
      (key, value) = bakerLabel(resource.metadata.name)
      _ <- io(k8s.delete[Service](service(resource).name))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.delete[Deployment](deployment(resource).name)),
        older = io(k8s.delete[skuber.ext.Deployment](oldDeployment(resource).name)))
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void,
        older = io(k8s.deleteAllSelected[skuber.ext.ReplicaSetList](LabelSelector(IsEqualRequirement(key, value)))).void)
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ = logger.info(s"Terminated baker cluster named '${resource.name}'")
    } yield ()

  def upgrade(resource: BakerResource, k8s: KubernetesClient): IO[Unit] =
    for {
      _ <- io(k8s.update[ConfigMap](configMap(resource))).void
      _ <- attemptOpOrTryOlderVersion(
        v1 = io(k8s.update[Deployment](deployment(resource))).void,
        older = io(k8s.update[skuber.ext.Deployment](oldDeployment(resource))).void)
      _ = logger.info(s"Upgraded baker cluster named '${resource.name}'")
    } yield ()

  private def stateNodeLabel: (String, String) = "app" -> "baas-state"

  private def bakerLabel(name: String): (String, String) = "baker-name" -> name

  private def akkaClusterLabel(selector: String): (String, String) = "akka-cluster" -> selector

  private def baasStateName(name: String): String = "baas-state-" + name

  private def baasStateServiceName(name: String): String = "baas-state-service-" + name

  private def baasRecipesConfigMapName(name: String): String = "baas-state-recipes-config-map-" + name

  private def baasStateServicePort: Int = 8081

  private def podSpec(bakerResource: BakerResource): Pod.Template.Spec = {

    val bakerName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = bakerLabel(bakerName)
    val image: String = bakerResource.spec.image
    val imagePullSecret: Option[String] = bakerResource.spec.imagePullSecret
    val serviceAccountSecret: Option[String] = bakerResource.spec.serviceAccountSecret
    val recipesMountPath: String = "/recipes"

    def stateNodeContainer = {
      val managementPort = Container.Port(
        name = "management",
        containerPort = 8558,
        protocol = Protocol.TCP
      )

      val stateNodeContainer = Container(
        name = baasStateName(bakerName),
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
        .exposePort(Container.Port(
          name = "http-api",
          containerPort = 8080,
          protocol = Protocol.TCP
        ))
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
        .setEnvVar("STATE_CLUSTER_SELECTOR", bakerName)
        .setEnvVar("RECIPE_DIRECTORY", recipesMountPath)
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")

      val stateNodeContainerWithResources =
        Utils.addResourcesSpec(stateNodeContainer, bakerResource.spec.resources)

      val stateContainerWithEventSink =
        bakerResource.spec.kafkaBootstrapServers.map(servers =>
          stateNodeContainerWithResources
            .setEnvVar("KAFKA_EVENT_SINK_BOOTSTRAP_SERVERS", servers)
            // todo add missing kafka configuration later (topics + identity missing)
            .setEnvVar("KAFKA_EVENT_SINK_ENABLED", "true")
        ).getOrElse(stateNodeContainerWithResources
          .setEnvVar("KAFKA_EVENT_SINK_ENABLED", "false"))

      val stateNodeContainerWithServiceAccount =
        if (serviceAccountSecret.isDefined)
          stateContainerWithEventSink.mount(name = "service-account-token", "/var/run/secrets/kubernetes.io/serviceaccount", readOnly = true)
        else
          stateContainerWithEventSink

      val stateNodeContainerWithExtraConfig =
        bakerResource.spec.config match {
          case Some(_) => stateNodeContainerWithServiceAccount.mount("extra-config", "/bakery-config", readOnly = true)
          case None => stateNodeContainerWithServiceAccount
        }

      val stateNodeContainerWithExtraSecrets =
        bakerResource.spec.secrets match {
          case Some(_) => stateNodeContainerWithExtraConfig.mount("extra-secrets", "/bakery-secrets", readOnly = true)
          case None => stateNodeContainerWithExtraConfig
        }
      stateNodeContainerWithExtraSecrets
    }

    def maybeSidecarContainer: Option[Container] = bakerResource.spec.sidecar map { sidecarSpec => {
      val sidecarContainer = Container(
        name = baasStateName(bakerName) + "-sidecar",
        image = sidecarSpec.image
      )
        .mount("config", sidecarSpec.configVolumeMountPath, readOnly = true)
        .setEnvVar("STATE_CLUSTER_SELECTOR", bakerName)
        .setEnvVar("RECIPE_DIRECTORY", recipesMountPath)
        .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")

      val stateNodeContainerWithResources =
        Utils.addResourcesSpec(stateNodeContainer, bakerResource.spec.resources)

      val stateContainerWithEventSink =
        bakerResource.spec.kafkaBootstrapServers.map(servers =>
          stateNodeContainerWithResources
            .setEnvVar("KAFKA_EVENT_SINK_BOOTSTRAP_SERVERS", servers)
            // todo add missing kafka configuration later (topics + identity missing)
            .setEnvVar("KAFKA_EVENT_SINK_ENABLED", "true")
        ).getOrElse(stateNodeContainerWithResources
          .setEnvVar("KAFKA_EVENT_SINK_ENABLED", "false"))

      val stateNodeContainerWithServiceAccount =
        if (serviceAccountSecret.isDefined)
          stateContainerWithEventSink.mount(name = "service-account-token", "/var/run/secrets/kubernetes.io/serviceaccount", readOnly = true)
        else
          stateContainerWithEventSink

      val stateNodeContainerWithExtraConfig =
        bakerResource.spec.config match {
          case Some(_) => stateNodeContainerWithServiceAccount.mount("extra-config", "/bakery-config", readOnly = true)
          case None => stateNodeContainerWithServiceAccount
        }

      val stateNodeContainerWithExtraSecrets =
        bakerResource.spec.secrets match {
          case Some(_) => stateNodeContainerWithExtraConfig.mount("extra-secrets", "/bakery-secrets", readOnly = true)
          case None => stateNodeContainerWithExtraConfig
        }
      stateNodeContainerWithExtraSecrets
    }

    val podSpec = Pod.Spec(
      containers = List(Some(stateNodeContainer), maybeSidecarContainer).flatten,
      imagePullSecrets = imagePullSecret.map(s => List(LocalObjectReference(s))).getOrElse(List.empty),
      volumes = List(
        Some(Volume("recipes", Volume.ConfigMapVolumeSource(baasRecipesConfigMapName(bakerName)))),
        serviceAccountSecret.map(s => Volume("service-account-token", Volume.Secret(s))),
        Some(Volume("config", Volume.))
        bakerResource.spec.config.map(c => Volume("extra-config", Volume.ConfigMapVolumeSource(c))),
        bakerResource.spec.secrets.map(s => Volume("extra-secrets", Volume.Secret(s)))
      ).flatten
    )

    Pod.Template.Spec
      .named(baasStateName(bakerName))
      .withPodSpec(podSpec)
      .addLabel(stateNodeLabel)
      .addLabel(bakerLabelWithName)
      .addLabel(akkaClusterLabel(bakerName))
  }

  private def deployment(bakerResource: BakerResource): Deployment = {

    val bakerName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = bakerLabel(bakerName)
    val replicas: Int = bakerResource.spec.replicas

    new Deployment(metadata = ObjectMeta(
      name = baasStateName(bakerName),
      labels = Map(stateNodeLabel, bakerLabelWithName) ++ bakerResource.metadata.labels.filter(_._1 != "custom-resource-definition")))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = bakerLabelWithName._1, value = bakerLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(bakerResource))
  }

  private def oldDeployment(bakerResource: BakerResource): skuber.ext.Deployment = {

    val bakerName: String = bakerResource.metadata.name
    val bakerLabelWithName: (String, String) = bakerLabel(bakerName)
    val replicas: Int = bakerResource.spec.replicas

    new skuber.ext.Deployment(metadata = ObjectMeta(
      name = baasStateName(bakerName),
      labels = Map(stateNodeLabel, bakerLabelWithName)
    ))
      .withLabelSelector(LabelSelector(LabelSelector.IsEqualRequirement(key = bakerLabelWithName._1, value = bakerLabelWithName._2)))
      .withReplicas(replicas)
      .withTemplate(podSpec(bakerResource))
  }

  def service(bakerResource: BakerResource): Service = {
    Service(baasStateServiceName(bakerResource.metadata.name))
      .addLabel("baas-component", "state")
      .addLabel("app", "baas-state-service")
      .addLabel("metrics" -> "collect")
      .addLabel(bakerLabel(bakerResource.metadata.name))
      .withSelector(bakerLabel(bakerResource.metadata.name))
      .setPorts(List(
        Service.Port(
          name = "http-api",
          port = baasStateServicePort,
          targetPort = Some(Right("http-api"))
        ),
        Service.Port(
          name = "prometheus",
          port = 9095,
          targetPort = Some(Right("prometheus"))
        )
      ))
  }

  private def configMap(bakerResource: BakerResource): ConfigMap = {
    val bakerName = bakerResource.metadata.name
    new ConfigMap(
      metadata = ObjectMeta(
        name = baasRecipesConfigMapName(bakerName),
        labels = Map(bakerLabel(bakerName))),
      data = bakerResource.recipes.get.map {
        case (serializedRecipe, compiledRecipe) => compiledRecipe.recipeId -> serializedRecipe
      }.toMap)
  }
}
