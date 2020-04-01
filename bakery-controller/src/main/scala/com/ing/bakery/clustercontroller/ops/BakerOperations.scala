package com.ing.bakery.clustercontroller.ops

import java.util.concurrent.Executors

import cats.syntax.functor._
import cats.effect.{ContextShift, IO}
import com.ing.bakery.clustercontroller.ResourceOperations
import com.ing.bakery.clustercontroller.ResourceOperations.ControllerSpecification
import skuber.api.client.KubernetesClient
import skuber.ext.Deployment
import skuber.{ConfigMap, Container, ObjectMeta, Pod, Protocol, Service, Volume}
import skuber.json.format._

import scala.concurrent.ExecutionContext

object BakerOperations {

  val spec: ControllerSpecification[BakerResource] =
    ControllerSpecification(service, deployment, r => bakerLabel(r.metadata.name), Some(hooks))

  val connectionPool: ExecutionContext =
    ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

  val stateNodeLabel: (String, String) = "app" -> "baas-state"

  def bakerLabel(name: String): (String, String) = "baker-name" -> name

  def akkaClusterLabel(selector: String): (String, String) = "akka-cluster" -> selector

  def baasStateName(name: String): String = "baas-state-" + name

  def baasStateServiceName(name: String): String = "baas-state-service-" + name

  def baasRecipesConfigMapName(name: String): String = "baas-state-recipes-config-map-" + name

  val baasStateServicePort: Int = 8081

  def deployment(bakerResource: BakerResource): Deployment = {

    val bakerName: String = bakerResource.metadata.name
    val bakeryVersion: String = bakerResource.spec.bakeryVersion
    val replicas: Int = bakerResource.spec.replicas
    val recipesMountPath: String = "/recipes"

    val managementPort = Container.Port(
      name = "management",
      containerPort = 8558,
      protocol = Protocol.TCP
    )

    val stateNodeContainer = Container(
      name = baasStateName(bakerName),
      image = "baas-node-state:" + bakeryVersion
    )
      // todo parametrise?
      .requestMemory("512M")
      .requestCPU("250m")
      .exposePort(Container.Port(
        name = "remoting",
        containerPort = 2552,
        protocol = Protocol.TCP
      ))
      .exposePort(managementPort)
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
        timeoutSeconds = 10
      ))
      .withLivenessProbe(skuber.Probe(
        action = skuber.HTTPGetAction(
          port = Right(managementPort.name),
          path = "/health/alive"
        ),
        initialDelaySeconds = 15,
        timeoutSeconds = 10
      ))
      .mount("recipes", recipesMountPath, readOnly = true)
      .setEnvVar("STATE_CLUSTER_SELECTOR", bakerName)
      .setEnvVar("RECIPE_DIRECTORY", recipesMountPath)
      .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")

    val podSpec = Pod.Spec(
      containers = List(stateNodeContainer),

      volumes = List(Volume("recipes", Volume.ConfigMapVolumeSource(baasRecipesConfigMapName(bakerName))))
    )

    val podTemplate = Pod.Template.Spec
      .named(baasStateName(bakerName))
      .withPodSpec(podSpec)
      .addLabel(stateNodeLabel)
      .addLabel(bakerLabel(bakerResource.name))
      .addLabel(akkaClusterLabel(bakerName))

    new Deployment(metadata = ObjectMeta(
      name = baasStateName(bakerName),
      labels = Map(stateNodeLabel, bakerLabel(bakerName))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  def service(bakerResource: BakerResource): Service = {
    Service(baasStateServiceName(bakerResource.metadata.name))
      .addLabel("baas-component", "state")
      .addLabel("app", "baas-state-service")
      .addLabel(bakerLabel(bakerResource.metadata.name))
      .withSelector(stateNodeLabel)
      .setPort(Service.Port(
        name = "http-api",
        port = baasStateServicePort,
        targetPort = Some(Right("http-api"))
      ))
  }

  def configMap(bakerResource: BakerResource): ConfigMap = {
    val bakerName = bakerResource.metadata.name
    new ConfigMap(
      metadata = ObjectMeta(
        name = baasRecipesConfigMapName(bakerName),
        labels = Map(bakerLabel(bakerName))),
      data = bakerResource.recipes.get.map {
        case (serializedRecipe, compiledRecipe) => compiledRecipe.recipeId -> serializedRecipe
      }.toMap)
  }
  
  def hooks: ResourceOperations.Hooks[BakerResource] =
    new ResourceOperations.Hooks[BakerResource] {
      override def preDeployment(resource: BakerResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        IO.fromFuture(IO(k8s.create[ConfigMap](configMap(resource)))).void
      override def preTermination(resource: BakerResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        IO.fromFuture(IO(k8s.delete[ConfigMap](baasRecipesConfigMapName(resource.metadata.name))))
      override def preUpdate(resource: BakerResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        IO.fromFuture(IO(k8s.update[ConfigMap](configMap(resource)))).void
    }

}
