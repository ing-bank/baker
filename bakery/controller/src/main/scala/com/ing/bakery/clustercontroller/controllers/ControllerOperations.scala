package com.ing.bakery.clustercontroller.controllers

import akka.{Done, NotUsed}
import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source}
import akka.stream.{KillSwitches, Materializer, UniqueKillSwitch}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.bakery.clustercontroller.controllers.Utils.FromConfigMapValidation
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.Format
import skuber.api.client.{EventType, KubernetesClient}
import skuber.{ConfigMap, K8SException, K8SWatchEvent, LabelSelector, ListOptions, ObjectResource, ResourceDefinition}

import scala.concurrent.Future
import scala.concurrent.duration._

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

  def watch(k8s: KubernetesClient, label: Option[(String, String)] = None, existsLabel: Option[String] = None)(
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
        case Left(e) =>
          IO(logger.error(s"Error when handling the event ${event._type} ${event._object.metadata.name}: " + e.getMessage))
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
      RestartSource.withBackoff(
        minBackoff = 3.seconds,
        maxBackoff = 30.seconds,
        randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
        maxRestarts = -1 // not limit the amount of restarts
      ) { () =>
        label
          .map(sourceWithLabel)
          .orElse(existsLabel.map(sourceWithExistsLabel))
          .getOrElse(sourceWithoutLabel)
          .mapError { case e =>
            logger.error(s"Error on the '${rd.spec.names.plural}' watch stream: " + e.getMessage, e)
            e
          }
      }.viaMat(KillSwitches.single)(Keep.right)

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

  /**
    * This attempts to make a skuber operation (normaly an api call to api version apps/v1), if the error is 404,
    * that means we are in an old kubernetes environment and we need to use an older version like extensions/apps/v1beta1
    */
  protected def attemptOpOrTryOlderVersion(v1: IO[Unit], older: IO[Unit]): IO[Unit] =
    v1.attempt.flatMap {
      case Left(e: K8SException) if e.status.code.contains(404) => older
      case Left(e) => IO.raiseError(e)
      case Right(a) => IO.pure(a)
    }

  /** Ensures idempotence from the Kubernetes api server creation calls, returns true if no-op, false if the operation was executed */
  protected def idem[A](ref: IO[A], name: String)(implicit cs: ContextShift[IO], rd: ResourceDefinition[O]): IO[Boolean] =
    ref.attempt.flatMap {
      case Left(e: K8SException) if e.status.code.contains(409) =>
        IO(logger.debug(s"ADDED ${rd.spec.names.kind} ($name already existed, trying next step)")) *> IO.pure(true)
      case Left(e) => IO.raiseError(e)
      case Right(_) => IO.pure(false)
    }

  protected def applyOrGet[A](ref: IO[A], orGet: IO[A], name: String)(implicit cs: ContextShift[IO], rd: ResourceDefinition[O]): IO[A] =
    ref.attempt.flatMap {
      case Left(e: K8SException) if e.status.code.contains(409) =>
        IO(logger.debug(s"ADDED ${rd.spec.names.kind} ($name already existed, will fetch it instead)")) *> orGet
      case Left(e) => IO.raiseError(e)
      case Right(a) => IO.pure(a)
    }

  protected def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
    IO.fromFuture(IO(ref))

}
