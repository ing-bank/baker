package com.ing.bakery.clustercontroller

import cats.implicits._
import akka.actor.ActorSystem
import akka.event.{Logging, LoggingAdapter}
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.api.client.{EventType, KubernetesClient}
import skuber.{K8SWatchEvent, ObjectResource, ResourceDefinition}

trait ResourceOperations[O <: ObjectResource] {
  def create: IO[Unit]
  def terminate: IO[Unit]
  def upgrade: IO[Unit]
}

object ResourceOperations extends LazyLogging {

  def controller[O <: ObjectResource](k8s: KubernetesClient, opsConstructor: (O, KubernetesClient) => ResourceOperations[O])(
    implicit
    contextShift: ContextShift[IO],
    timer: Timer[IO],
    actorSystem: ActorSystem,
    materializer: Materializer,
    fmt: Format[O],
    rd: ResourceDefinition[O]
  ): Resource[IO, Unit] = {

    implicit val akkaLogger: LoggingAdapter = Logging(actorSystem, rd.spec.names.kind + "-Controller")

    def handleEvent(event: K8SWatchEvent[O]): IO[Unit] = {
      akkaLogger.info(event._type + " " + event._object.metadata.name)
      val ops = opsConstructor(event._object, k8s)
      (event._type match {
        case EventType.ADDED => ops.create
        case EventType.DELETED => ops.terminate
        case EventType.MODIFIED => ops.upgrade
        case EventType.ERROR => IO(akkaLogger.error(s"Event type ERROR on ${rd.spec.names.kind} CRD: ${event._object}"))
      }).attempt.flatMap {
        case Left(e) => IO(akkaLogger.error(s"Error when handling the event ${event._type}: " + e.getMessage))
        case Right(_) => IO.unit
      }
    }

    //val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())
    val sink = Sink
      .foreach[Option[K8SWatchEvent[O]]] {
        case Some(event) =>
          handleEvent(event).recover { case e =>
            println(Console.RED + e + Console.RESET)
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
            akkaLogger.error("Serialization or CRD consistency issue:" + e.getMessage)
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
