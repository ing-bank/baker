package com.ing.bakery.clustercontroller

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.typesafe.scalalogging.Logger
import play.api.libs.json.Format
import skuber.api.client.{EventType, KubernetesClient}
import skuber.{K8SWatchEvent, ObjectResource, ResourceDefinition}

trait ResourceOperations[O <: ObjectResource] {
  def create: IO[Unit]
  def terminate: IO[Unit]
  def upgrade: IO[Unit]
}

object ResourceOperations {

  val logger: Logger = Logger("bakery.ResourceOperations")

  def controller[O <: ObjectResource](k8s: KubernetesClient, opsConstructor: (O, KubernetesClient) => ResourceOperations[O])(
    implicit
    contextShift: ContextShift[IO],
    timer: Timer[IO],
    actorSystem: ActorSystem,
    materializer: Materializer,
    fmt: Format[O],
    rd: ResourceDefinition[O]
  ): Resource[IO, Unit] = {

    def handleEvent(event: K8SWatchEvent[O]): IO[Unit] = {
      logger.info(event._type + " " + event._object.metadata.name)
      val ops = opsConstructor(event._object, k8s)
      (event._type match {
        case EventType.ADDED => ops.create
        case EventType.DELETED => ops.terminate
        case EventType.MODIFIED => ops.upgrade
        case EventType.ERROR => IO(logger.error(s"Event type ERROR on ${rd.spec.names.kind} CRD: ${event._object}"))
      }).attempt.flatMap {
        case Left(e) => IO(logger.error(s"Error when handling the event ${event._type}: " + e.getMessage))
        case Right(_) => IO.unit
      }
    }

    //val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())
    val sink = Sink
      .foreach[Option[K8SWatchEvent[O]]] {
        case Some(event) =>
          handleEvent(event).recover { case e =>
            logger.error(s"While processing watch events on controller: ${e.getMessage}", e)
          }.unsafeToFuture()
        case None =>
          Unit
      }

    val create = for {
      killSwitch <- IO {
        //TODO chose a more reasonable numbre for the bufSize
        k8s.watchAllContinuously[O](bufSize = Int.MaxValue)
          .map(Some(_))
          .recover { case e =>
            logger.error("Serialization or CRD consistency issue:" + e.getMessage, e)
            None
          }
          .viaMat(KillSwitches.single)(Keep.right)
          .toMat(sink)(Keep.left)
          .run()
      }
      _ = sys.addShutdownHook(killSwitch.shutdown())
    } yield IO(killSwitch.shutdown())

    Resource.make(create)(identity).map(_ => ())
  }
}
