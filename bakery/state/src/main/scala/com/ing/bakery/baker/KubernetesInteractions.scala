package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source, TcpIdleTimeoutException}
import akka.stream.{KillSwitch, KillSwitches, Materializer, RestartSettings, UniqueKillSwitch}
import akka.{Done, NotUsed}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits.catsSyntaxApplicativeError
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.ing.baker.runtime.model.InteractionInstance
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._
import skuber.{K8SWatchEvent, LabelSelector, ListOptions, Service}

import scala.concurrent.Future
import scala.concurrent.duration.DurationInt

class KubernetesInteractions(config: Config,
                             system: ActorSystem,
                             val client: Client[IO],
                             kubernetes: KubernetesClient)
  extends DynamicInteractionManager
    with RemoteInteractionDiscovery
    with LazyLogging {

  private implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  private implicit val timer: Timer[IO] = IO.timer(system.dispatcher)

  private val path = config.getString("baker.interactions.api-url-prefix")

  override def resource: Resource[IO, DynamicInteractionManager] = {

    def noneIfEmpty(str: String) = if (str.isEmpty) None else Some(str)

    val podLabelSelector = noneIfEmpty(config.getString("baker.interactions.pod-label-selector"))
      .map(_.split("="))
      .map { kv => LabelSelector(LabelSelector.IsEqualRequirement(kv(0), kv(1))) }

    def watchSource: Source[K8SWatchEvent[Service], UniqueKillSwitch] = {
      val watchFilter: ListOptions = ListOptions(labelSelector = podLabelSelector)
      /*, timeoutSeconds = Some(45)*/ // Note, we decided to go for long connections against renewing every 45 seconds due an issue with OpenShift 3.11 not being able to respond to calls with resourceVersion as supposed to be

      // todo how do we ensure that connection on the long poll is not dead?
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
          case e: TcpIdleTimeoutException  => e // expected to happen
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

      case EventType.ADDED | EventType.MODIFIED => for {
        interfaces <- extractInterfacesFromDeployedInteraction(client, event._object, port.port, path)
        d <- discovered
      } yield d.put(event._object.name, interfaces)

      case EventType.DELETED => for {
        d <- discovered
      } yield d.remove(event._object.name)

      case EventType.ERROR =>
        IO(logger.error(s"Event type ERROR on service watch for service ${event._object}"))
    }
  }) getOrElse IO.unit

  def extractInterfacesFromDeployedInteraction(httpClient: Client[IO], deployedService: Service, port: Int, path: String)
                                              (implicit contextShift: ContextShift[IO], timer: Timer[IO])
  : IO[List[InteractionInstance[IO]]] =
    extractInteractions(httpClient, Uri.unsafeFromString(s"http://${deployedService.name}:$port$path"))

}
