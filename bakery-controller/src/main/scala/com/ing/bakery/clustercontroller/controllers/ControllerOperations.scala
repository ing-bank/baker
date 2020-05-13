package com.ing.bakery.clustercontroller.controllers

import akka.{Done, NotUsed}
import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink, Source}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.api.client.{EventType, KubernetesClient}
import skuber.{ConfigMap, K8SException, K8SWatchEvent, LabelSelector, ListOptions, ObjectResource, ResourceDefinition}

import scala.concurrent.Future

trait ControllerOperations[O <: ObjectResource] extends LazyLogging { self =>

  def create(resource: O, k8s: KubernetesClient): IO[Unit]

  def terminate(resource: O, k8s: KubernetesClient): IO[Unit]

  def upgrade(resource: O, k8s: KubernetesClient): IO[Unit]

  def fromConfigMaps(from: ConfigMap => FromConfigMapValidation[O])(implicit rd: ResourceDefinition[O]): ControllerOperations[ConfigMap] = {
    def validate(resource: ConfigMap): IO[O] =
      from(resource).fold(
        errs => IO.raiseError(new RuntimeException(s"Could not transform ConfigMap into ${rd.spec.names.kind}: ${errs.mkString_(" and ")}")),
        IO.pure
      )
    new ControllerOperations[ConfigMap] {
      override def create(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.create(_, k8s))
      override def terminate(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.terminate(_, k8s))
      override def upgrade(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.upgrade(_, k8s))
    }
  }

  def watch(k8s: KubernetesClient, label: Option[(String, String)] = None)(
    implicit
    contextShift: ContextShift[IO],
    timer: Timer[IO],
    actorSystem: ActorSystem,
    materializer: Materializer,
    fmt: Format[O],
    rd: ResourceDefinition[O]
  ): Resource[IO, Unit] = {

    def handleEvent(event: K8SWatchEvent[O]): IO[Unit] = {
      (event._type match {
        case EventType.ADDED => create(event._object, k8s)
        case EventType.DELETED => terminate(event._object, k8s)
        case EventType.MODIFIED => upgrade(event._object, k8s)
        case EventType.ERROR => IO(logger.error(s"Event type ERROR on ${rd.spec.names.kind} CRD: ${event._object}"))
      }).attempt.flatMap {
        case Left(e: K8SException) if e.status.code.contains(409) =>
          IO(logger.info(event._type + " " + event._object.metadata.name + " (resource already existed)"))
        case Left(e) =>
          IO(logger.error(s"Error when handling the event ${event._type} ${event._object.metadata.name}: " + e.getMessage))
        case Right(_) =>
          IO(logger.info(event._type + " " + event._object.metadata.name))
      }
    }

    //TODO chose a more reasonable number for the bufSize
    def sourceWithLabel(keyValue: (String, String)): Source[K8SWatchEvent[O], NotUsed] = {
      val watchFilter: ListOptions = {
        val labelSelector = LabelSelector(LabelSelector.IsEqualRequirement(keyValue._1, keyValue._2))
        ListOptions(labelSelector = Some(labelSelector), timeoutSeconds = Some(30))
      }
      k8s.watchWithOptions(watchFilter, bufsize = Int.MaxValue)
        .mapMaterializedValue(_ => NotUsed)
    }

    //TODO chose a more reasonable number for the bufSize
    def sourceWithoutLabel: Source[K8SWatchEvent[O], NotUsed] =
      k8s.watchAllContinuously[O](bufSize = Int.MaxValue)
        .mapMaterializedValue(_ => NotUsed)

    def source: Source[K8SWatchEvent[O], NotUsed] =
      label.fold(sourceWithoutLabel)(sourceWithLabel)

    def sourceWithRetry: Source[K8SWatchEvent[O], NotUsed] =
      source.recoverWithRetries(-1, { case e =>
        logger.error(s"Error on the '${rd.spec.names.plural}' watch stream: " + e.getMessage, e)
        source
      })

    val sink: Sink[K8SWatchEvent[O], Future[Done]] =
      Sink.foreach[K8SWatchEvent[O]] { event =>
        handleEvent(event)
          .recover { case e => logger.error(s"Error while processing watch event ${event._type} of controller for '${rd.spec.names.plural}': ${e.getMessage}", e) }
          .unsafeToFuture()
      }

    Resource.make(
      IO(sourceWithRetry
        .viaMat(KillSwitches.single)(Keep.right)
        .toMat(sink)(Keep.left).run())
        .map { killSwitch =>
          sys.addShutdownHook(killSwitch.shutdown())
          IO(killSwitch.shutdown())
        }
    )(identity).map(_ => ())
  }
}
