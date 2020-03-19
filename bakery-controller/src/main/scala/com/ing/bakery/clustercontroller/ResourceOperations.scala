package com.ing.bakery.clustercontroller

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.{EventType, KubernetesClient}
import skuber.ext.{Deployment, ReplicaSetList}
import skuber.json.ext.format._
import skuber.json.format._
import skuber.{K8SWatchEvent, LabelSelector, ObjectResource, PodList, ResourceDefinition, Service}

import scala.concurrent.Future

object ResourceOperations extends LazyLogging {

  case class ControllerSpecification[O <: ObjectResource](
    service: O => Service,
    deployment: O => Deployment,
    label: O => (String, String),
    hooks: Option[Hooks[O]] = None
  )

  trait Hooks[O <: ObjectResource] {
    def preDeployment(resource: O, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit]
    def preTermination(resource: O, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit]
    def preUpdate(resource: O, k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[Unit]
  }

  def controller[O <: ObjectResource](k8s: KubernetesClient, spec: ControllerSpecification[O])(
    implicit
    contextShift: ContextShift[IO],
    timer: Timer[IO],
    actorSystem: ActorSystem,
    materializer: Materializer,
    fmt: Format[O],
    rd: ResourceDefinition[O]
  ): Resource[IO, Unit] = {

    val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())

    def handleEvent(event: K8SWatchEvent[O]): IO[Unit] = {
      val ops = new ResourceOperations[O](event._object, spec, k8s)
      println(Console.YELLOW + event._type + " " + event._object.metadata.name + Console.RESET)
      event._type match {
        case EventType.ADDED => ops.create
        case EventType.DELETED => ops.terminate
        case EventType.MODIFIED => ops.upgrade
        case EventType.ERROR => IO(logger.error(s"Event type ERROR on Recipe CRD watch for recipe ${event._object}"))
      }
    }

    val create = for {
      killSwitch <- IO {
        k8s.watchAllContinuously[O]()
          .viaMat(KillSwitches.single)(Keep.right)
          .toMat(Sink.foreachAsync(paralellism)(handleEvent(_).unsafeToFuture()))(Keep.left)
          .run()
      }
      _ = sys.addShutdownHook(killSwitch.shutdown())
    } yield IO(killSwitch.shutdown())

    Resource.make(create)(identity).map(_ => ())
  }
}

final class ResourceOperations[O <: ObjectResource](resource: O, spec: ResourceOperations.ControllerSpecification[O], k8s: KubernetesClient)
                                                   (implicit cs: ContextShift[IO], timer: Timer[IO], fmt: Format[O], rd: ResourceDefinition[O]) extends LazyLogging {

  private def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))

  def create: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Creating ${rd.spec.names.kind}: ${resource.name}"))
      _ <- spec.hooks.fold(IO.unit)(_.preDeployment(resource, k8s))
      _ <- io(k8s.create(spec.deployment(resource)))
      _ <- io(k8s.create(spec.service(resource)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }

  def terminate: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Deleting ${rd.spec.names.kind}: ${resource.name}"))
      _ <- spec.hooks.fold(IO.unit)(_.preTermination(resource, k8s))
      (key, value) = spec.label(resource)
      _ <- io(k8s.delete[Service](spec.service(resource).name))
      _ <- io(k8s.delete[Deployment](spec.deployment(resource).name))
      _ <- io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value))))
      _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }

  def upgrade: IO[Unit] =
    (for {
      _ <- IO(logger.info(s"Updating ${rd.spec.names.kind}: ${resource.name}"))
      _ <- spec.hooks.fold(IO.unit)(_.preUpdate(resource, k8s))
      _ <- io(k8s.update[skuber.ext.Deployment](spec.deployment(resource)))
    } yield ()).attempt.flatMap {
      case Left(e) => IO(println(Console.RED + e.getMessage + Console.RESET))
      case _ => IO.unit
    }
}
