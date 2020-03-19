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

object RecipeOperations {

  val spec: ControllerSpecification[RecipeResource] =
    ControllerSpecification(service, deployment, r => recipeLabel(r.recipeId.get), Some(hooks))

  val connectionPool: ExecutionContext =
    ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

  val stateNodeLabel: (String, String) = "app" -> "baas-state"

  def recipeLabel(recipeId: String): (String, String) = "recipe" -> recipeId

  def akkaClusterLabel(selector: String): (String, String) = "akka-cluster" -> selector

  def baasStateName(recipeId: String): String = "baas-state-" + recipeId

  def baasStateServiceName(recipeId: String): String = "baas-state-service-" + recipeId

  def baasRecipesConfigMapName(recipeId: String): String = "baas-state-recipes-config-map-" + recipeId

  val baasStateServicePort: Int = 8081

  def deployment(recipe: RecipeResource): Deployment = {

    val recipeId = recipe.recipeId.get
    val bakeryVersion: String = recipe.spec.bakeryVersion
    val replicas: Int = recipe.spec.replicas
    val recipesMountPath: String = "/recipes"

    val managementPort = Container.Port(
      name = "management",
      containerPort = 8558,
      protocol = Protocol.TCP
    )

    val stateNodeContainer = Container(
      name = baasStateName(recipeId),
      image = "baas-node-state:" + bakeryVersion
    )
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
        )
      ))
      .withLivenessProbe(skuber.Probe(
        action = skuber.HTTPGetAction(
          port = Right(managementPort.name),
          path = "/health/alive"
        )
      ))
      .mount("recipes", recipesMountPath, readOnly = true)
      .setEnvVar("STATE_CLUSTER_SELECTOR", recipeId)
      .setEnvVar("RECIPE_DIRECTORY", recipesMountPath)

    val podSpec = Pod.Spec(
      containers = List(stateNodeContainer),
      volumes = List(Volume("recipes", Volume.ConfigMapVolumeSource(baasRecipesConfigMapName(recipeId))))
    )

    val podTemplate = Pod.Template.Spec
      .named(baasStateName(recipeId))
      .withPodSpec(podSpec)
      .addLabel(stateNodeLabel)
      .addLabel(recipeLabel(recipeId))
      .addLabel(akkaClusterLabel(recipeId))

    new Deployment(metadata = ObjectMeta(
      name = baasStateName(recipeId),
      labels = Map(stateNodeLabel, recipeLabel(recipeId))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  def service(recipe: RecipeResource): Service = {
    val recipeId = recipe.recipeId.get
    Service(baasStateServiceName(recipeId))
      .withLoadBalancerType
      .addLabel("baas-component", "state")
      .addLabel("app", "baas-state-service")
      .addLabel(recipeLabel(recipeId))
      .withSelector(stateNodeLabel)
      .setPort(Service.Port(
        name = "http-api",
        port = baasStateServicePort,
        targetPort = Some(Right("http-api"))
      ))
  }
  
  def hooks: ResourceOperations.Hooks[RecipeResource] =
    new ResourceOperations.Hooks[RecipeResource] {
      override def preDeployment(resource: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        loadRecipeFiles(resource, k8s)
      override def preTermination(resource: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        cleanConfigMap(resource, k8s)
      override def preUpdate(resource: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
        IO.unit
    }

  def loadRecipeFiles(recipe: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] = {
    val recipeId = recipe.recipeId.get
    val configMap = new ConfigMap(
      metadata = ObjectMeta(
        name = baasRecipesConfigMapName(recipeId),
        labels = Map(recipeLabel(recipeId))),
      data = Map(recipe.name -> recipe.spec.recipe)
    )
    IO.fromFuture(IO(k8s.create[ConfigMap](configMap))).void
  }

  def cleanConfigMap(recipe: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit] =
    IO.fromFuture(IO(k8s.delete[ConfigMap](baasRecipesConfigMapName(recipe.recipeId.get))))
}
