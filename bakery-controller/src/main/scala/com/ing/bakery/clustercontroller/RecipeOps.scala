package com.ing.bakery.clustercontroller

import java.util.concurrent.Executors

import cats.effect.{ContextShift, IO, Timer}
import cats.syntax.apply._
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.bakery.clustercontroller.RecipeOps._
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.ext.{Deployment, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{Container, LabelSelector, ObjectMeta, Pod, PodList, Protocol, Service}

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

object RecipeOps {

  val connectionPool: ExecutionContext =
    ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

  val stateNodeLabel: (String, String) = "app" -> "baas-state"

  def recipeLabel(recipeId: String): (String, String) = "recipe" -> recipeId

  def akkaClusterLabel(selector: String): (String, String) = "akka-cluster" -> selector

  val namespace: String = "default"

  def baasStateName(recipeId: String): String = "baas-state-" + recipeId

  def baasStateServiceName(recipeId: String): String = "baas-state-service-" + recipeId

  val baasStateServicePort: Int = 8081

  def deployment(recipeId: String, bakeryVersion: String, replicas: Int): Deployment = {
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
      .setEnvVar("STATE_CLUSTER_SELECTOR", recipeId)

    val podTemplate = Pod.Template.Spec
      .named(baasStateName(recipeId))
      .addContainer(stateNodeContainer)
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

  def service(recipeId: String) = {
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

  def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

  def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))
}

final class RecipeOps(resource: RecipeResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends LazyLogging {

  def createBakeryCluster: IO[Unit] = {
    (for {
      compiledRecipe <- resource.decodeRecipe
      recipeId = compiledRecipe.recipeId
      _ = logger.info(s"Creating baker cluster for recipe '$recipeId'")
      _ <- io(k8s.create(deployment(recipeId, resource.spec.bakeryVersion, resource.spec.replicas)))
      service <- io(k8s.create(service(recipeId)))
      stateAccessUri = Uri.unsafeFromString(s"http://${service.metadata.name}:$baasStateServicePort")
      _ <- BakerClient.resource(stateAccessUri, connectionPool).use(client =>
        within(30.seconds, split = 30)(io(client.addRecipe(compiledRecipe))))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }
  }

  def terminateBakeryCluster: IO[Unit] =
    (for {
      compiledRecipe <- resource.decodeRecipe
      recipeId = compiledRecipe.recipeId
      _ = logger.info(s"Updating baker cluster for recipe '$recipeId'")
      (key, value) = recipeLabel(recipeId)
      _ <- io(k8s.delete[skuber.ext.Deployment](name = baasStateName(recipeId)))
      _ <- io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.delete[skuber.Service](name = baasStateServiceName(recipeId)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }

  def upgradeBakeryCluster: IO[Unit] =
    (for {
      compiledRecipe <- resource.decodeRecipe
      recipeId = compiledRecipe.recipeId
      _ = logger.info(s"Deleting baker cluster for recipe '$recipeId'")
      _ <- io(k8s.update[skuber.ext.Deployment] (deployment(recipeId, resource.spec.bakeryVersion, resource.spec.replicas)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }
}
