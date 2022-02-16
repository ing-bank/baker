package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.stream._
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source, TcpIdleTimeoutException}
import akka.{Done, NotUsed}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits.catsSyntaxApplicativeError
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._
import skuber.{K8SWatchEvent, LabelSelector, ListOptions, Service}

import scala.concurrent.Future
import scala.concurrent.duration.DurationInt

/**
  * Discovers interactions in the same namespace using Kubernetes pod lookup.
  */
class KubernetesInteractions(config: Config,
                             system: ActorSystem,
                             val client: RemoteInteractionClient,
                             kubernetesClient: Option[KubernetesClient] = None)
  extends DynamicInteractionManager
    with RemoteInteractionDiscovery
    with LazyLogging {

  private implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  private implicit val timer: Timer[IO] = IO.timer(system.dispatcher)

  private val apiUrlPrefix = config.getString("baker.interactions.kubernetes.api-url-prefix")
  private val kubernetes = kubernetesClient.getOrElse(skuber.k8sInit(config)(system))

  override def resource: Resource[IO, DynamicInteractionManager] = {

    def noneIfEmpty(str: String): Option[String] = if (str.isEmpty) None else Some(str)

    val podLabelSelector = noneIfEmpty(config.getString("baker.interactions.kubernetes.pod-label-selector"))
      .map(_.split("="))
      .map { kv => LabelSelector(LabelSelector.IsEqualRequirement(kv(0), kv(1))) }

    def watchSource: Source[K8SWatchEvent[Service], UniqueKillSwitch] = {
      val watchFilter: ListOptions = ListOptions(labelSelector = podLabelSelector)

      def source: Source[K8SWatchEvent[Service], NotUsed] =
        kubernetes
          .watchWithOptions[Service](watchFilter, bufsize = Int.MaxValue)
          .mapMaterializedValue(_ => NotUsed)

      RestartSource.withBackoff(RestartSettings(
        minBackoff = 3.seconds,
        maxBackoff = 30.seconds,
        randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
      )) { () =>
        source.mapError {
          case e: TcpIdleTimeoutException => e // expected to happen
          case e =>
            logger.error("Interaction discovery watch stream error: " + e.getMessage, e)
            e
        }
      }.viaMat(KillSwitches.single)(Keep.right)
    }

    def updateSink: Sink[K8SWatchEvent[Service], Future[Done]] = {
      Sink.foreach[K8SWatchEvent[Service]] { event =>
        logger.info(s"Interaction service ${event._type} @ ${event._object.name}")
        update(event).recover { case e =>
          logger.error("Failure when updating the services in the ConfigMap Discovery component", e)
        }.unsafeToFuture()
      }
    }

    Resource.make(for {
      killSwitch <- IO {
        if (podLabelSelector.isDefined) {
          logger.info(s"Watching interaction services: ${podLabelSelector.getOrElse("")}")
          watchSource
            .toMat(updateSink)(Keep.left)
            .run()(Materializer.matFromSystem(system))
        } else {
          logger.info("Pod selector not specified, watching interaction services not enabled")
          new KillSwitch {
            override def shutdown(): Unit = ()

            override def abort(ex: Throwable): Unit = ()
          }
        }
      }
    } yield (this, killSwitch)) { case (_, hook) => IO(hook.shutdown()) }.map(_._1)
  }

  def update(event: K8SWatchEvent[Service])(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Any] = (for {
    spec <- event._object.spec
    port <- spec.ports.find(_.name == "interactions")
  } yield {
    event._type match {

      case EventType.ADDED | EventType.MODIFIED =>
        val url = s"http://${event._object.name}:${port.port}$apiUrlPrefix"
        for {
          remoteInteractions <- extractInteractions(client, Uri.unsafeFromString(url))
          d <- discovered
          _ <- clearTransitionCache()
        } yield {
          logger.info(s"${url} (${event._object.name}) provides ${remoteInteractions.interactions.size} interactions: ${remoteInteractions.interactions.map(_.name).mkString(",")}")
          d.put(event._object.name, InteractionBundle(remoteInteractions.startedAt, remoteInteractions.interactions))
        }

      case EventType.DELETED => for {
        d <- discovered
        _ <- clearTransitionCache()
      } yield {
        logger.info(s"${event._object.name} interaction service was removed")
        d.remove(event._object.name)
      }

      case EventType.ERROR =>
        IO(logger.error(s"Event type ERROR on service watch for service ${event._object}"))
    }
  }) getOrElse IO.unit


}
