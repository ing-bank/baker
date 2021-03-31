package com.ing.bakery.clustercontroller.controllers

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source}
import akka.stream.{KillSwitches, Materializer, RestartSettings, UniqueKillSwitch}
import akka.{Done, NotUsed}
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.api.client.{EventType, KubernetesClient, LoggingContext}
import skuber.{ConfigMap, K8SException, K8SWatchEvent, LabelSelector, ListOptions, ObjectResource, ResourceDefinition}

import scala.concurrent.Future
import scala.concurrent.duration._
import cats.effect.Temporal

object ControllerOperations extends LazyLogging {

  /** This utility is intended for Kubernetes operations, normally an api call to api version apps/v1, if the error is 404,
    * that means we are in an old kubernetes environment and we need to use an older version like extensions/apps/v1beta1
    */
  def attemptOpOrTryOlderVersion[A, B](v1: => IO[A], older: => IO[B]): IO[Either[A, B]] =
    v1.map(Left(_)).handleErrorWith {
      case e: K8SException if e.status.code.contains(404) =>
        older.map(Right(_))
      case e => 
        IO.raiseError(e)
    }

  /** Ensures idempotent create of a Kubernetes resource.
    *
    * @param resource to be created
    * @return true if no-op because a resource with the same name already existed, false if the operation was executed.
    */
  def idemCreate[O <: ObjectResource](resource: O)(implicit rd: ResourceDefinition[O], fmt: Format[O], l: LoggingContext, k8s: KubernetesClient): IO[Boolean] =
    io(k8s.create(resource)).map(_ => false).handleErrorWith {
      case e: K8SException if e.status.code.contains(409) =>
        logger.debug(s"ADDED ${rd.spec.names.kind} (already existed, trying next step)")
        IO.pure(true)
      case e => 
        IO.raiseError(e)
    }

  def createOrFetch[O <: ObjectResource](resource: O)(implicit rd: ResourceDefinition[O], fmt: Format[O], l: LoggingContext, k8s: KubernetesClient): IO[O] =
    io(k8s.create(resource)).handleErrorWith {
      case e: K8SException if e.status.code.contains(409) =>
        logger.debug(s"ADDED ${rd.spec.names.kind} (already existed, will fetch it instead)") 
        io(k8s.get(resource.name))
      case e => 
        IO.raiseError(e)
    }

  /** Cleaner transform from scala Future to cats IO
    */
  def io[A](ref: => Future[A]): IO[A] =
    IO.fromFuture(IO.delay(ref))
}

trait ControllerOperations[O <: ObjectResource] extends LazyLogging { self =>

  def create(resource: O)(implicit k8s: KubernetesClient): IO[Unit]

  def terminate(resource: O)(implicit k8s: KubernetesClient): IO[Unit]

  def upgrade(resource: O)(implicit k8s: KubernetesClient): IO[Unit]

  def fromConfigMaps(from: ConfigMap => FromConfigMapValidation[O])(implicit rd: ResourceDefinition[O]): ControllerOperations[ConfigMap] = {
    def validate(resource: ConfigMap): IO[O] =
      from(resource).fold(
        errs => IO.raiseError(new RuntimeException(s"Could not transform ConfigMap into ${rd.spec.names.kind}: ${errs.toList.mkString(" and ")}")),
        IO.pure
      )
    new ControllerOperations[ConfigMap] {
      override def create(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.create)
      override def terminate(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.terminate)
      override def upgrade(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] =
        validate(resource).flatMap(self.upgrade)
    }
  }

  def runController(labelFilter: Option[(String, String)] = None, existsLabelFilter: Option[String] = None)(
    implicit
    timer: Temporal[IO],
    actorSystem: ActorSystem,
    materializer: Materializer,
    fmt: Format[O],
    rd: ResourceDefinition[O],
    k8s: KubernetesClient
  ): Resource[IO, Unit] = {

    def handleEvent(event: K8SWatchEvent[O]): IO[Unit] = {
      (event._type match {
        case EventType.ADDED =>
          create(event._object)
        case EventType.DELETED =>
          terminate(event._object)
        case EventType.MODIFIED =>
          upgrade(event._object)
        case EventType.ERROR =>
          IO(logger.error(s"Event type ERROR on ${rd.spec.names.kind} CRD: ${event._object}"))
      }).attempt.flatMap {
        case Left(e) =>
          IO(logger.error(s"Error when handling the event ${event._type} ${event}: " + e.getMessage, e))
        case Right(_) =>
          IO.unit
      }
    }

    def sourceWithLabel(keyValue: (String, String)): Source[K8SWatchEvent[O], NotUsed] =
      sourceWithOptions({
        val labelSelector = LabelSelector(LabelSelector.IsEqualRequirement(keyValue._1, keyValue._2))
        ListOptions(labelSelector = Some(labelSelector)/*, timeoutSeconds = Some(45)*/) // Note, we decided to go for long connections against renewing every 45 seconds due an issue with OpenShift 3.11 not being able to respond to calls with resourceVersion as supposed to be
      })

    def sourceWithExistsLabel(key: String): Source[K8SWatchEvent[O], NotUsed] =
      sourceWithOptions({
        val labelSelector = LabelSelector(LabelSelector.ExistsRequirement(key))
        ListOptions(labelSelector = Some(labelSelector)/*, timeoutSeconds = Some(45)*/) // Note, we decided to go for long connections against renewing every 45 seconds due an issue with OpenShift 3.11 not being able to respond to calls with resourceVersion as supposed to be
      })

    def sourceWithOptions(listOptions: ListOptions): Source[K8SWatchEvent[O], NotUsed] =
      k8s.watchWithOptions(listOptions, bufsize = Int.MaxValue)
        .mapMaterializedValue(_ => NotUsed)

    //TODO chose a more reasonable number for the bufSize
    def sourceWithoutLabel: Source[K8SWatchEvent[O], NotUsed] =
      k8s.watchAllContinuously[O](bufSize = Int.MaxValue)
        .mapMaterializedValue(_ => NotUsed)

    def sourceWithRetry: Source[K8SWatchEvent[O], UniqueKillSwitch] =
      RestartSource.withBackoff(RestartSettings(
        minBackoff = 3.seconds,
        maxBackoff = 30.seconds,
        randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
      )) { () =>
        labelFilter
          .map(sourceWithLabel)
          .orElse(existsLabelFilter.map(sourceWithExistsLabel))
          .getOrElse(sourceWithoutLabel)
          .mapError { case e =>
            logger.error(s"Error on the '${rd.spec.names.plural}' watch stream: " + e.getMessage, e)
            e
          }
      }.viaMat(KillSwitches.single)(Keep.right)

    val sink: Sink[K8SWatchEvent[O], Future[Done]] =
      Sink.foreach[K8SWatchEvent[O]] { event =>
        handleEvent(event)
          .redeem(
            e => logger.error(s"Error while processing watch event ${event._type} of controller for '${rd.spec.names.plural}': ${e.getMessage}", e),
            identity
          )
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
