package com.ing.bakery.clustercontroller

import cats.effect.{ContextShift, IO, Timer}
import com.ing.bakery.clustercontroller.InteractionOps._
import com.typesafe.scalalogging.LazyLogging
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.ext.{Deployment, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{Container, LabelSelector, ObjectMeta, Pod, PodList, Protocol, Service}

import scala.concurrent.Future

object InteractionOps {

  def interactionLabel(name: String): (String, String) = "app" -> name

  def serviceName(name: String): String = name + "-interaction-service"

  val baasComponentLabel: (String, String) = "baas-component" -> "remote-interaction"

  val httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  def deployment(name: String, image: String, replicas: Int): Deployment = {

    val healthProbe = skuber.Probe(
      action = skuber.HTTPGetAction(
        port = Right(httpAPIPort.name),
        path = "/api/v3/health"
      )
    )

    val interactionContainer = Container(
      name = name,
      image = image)
      .exposePort(httpAPIPort)
      .withReadinessProbe(healthProbe)
      .withLivenessProbe(healthProbe)

    val podTemplate = Pod.Template.Spec
      .named(name)
      .addContainer(interactionContainer)
      .addLabel(interactionLabel(name))

    new Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(interactionLabel(name))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  def service(name: String): Service = {
    Service(serviceName(name))
      .withLoadBalancerType
      .addLabel(baasComponentLabel)
      .withSelector(interactionLabel(name))
      .setPort(Service.Port(
        name = httpAPIPort.name,
        port = httpAPIPort.containerPort
      ))
  }

  def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))
}


final class InteractionOps(resource: InteractionResource, k8s: KubernetesClient)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends LazyLogging {

  def createInteraction: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Creating Interaction: ${resource.name}"))
      _ <- io(k8s.create(deployment(resource.name, resource.spec.image, resource.spec.replicas)))
      _ <- io(k8s.create(service(resource.name)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }


  def terminateBakeryCluster: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Deleting Interaction: ${resource.name}"))
      (key, value) = interactionLabel(resource.name)
      _ <- io(k8s.delete[skuber.ext.Deployment](name = resource.name))
      _ <- io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.delete[skuber.Service](name = serviceName(resource.name)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }

  def upgradeBakeryCluster: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Updating Interaction: ${resource.name}"))
      _ <- io(k8s.update[skuber.ext.Deployment](deployment(resource.name, resource.spec.image, resource.spec.replicas)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }
}
