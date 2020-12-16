package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source}
import akka.stream.{KillSwitches, RestartSettings, UniqueKillSwitch}
import akka.{Done, NotUsed}
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Sync, Timer}
import cats.implicits._
import cats.Applicative
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import com.ing.bakery.interaction.RemoteInteractionClient
import com.ing.bakery.protocol.InteractionExecution
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import skuber._
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._

import scala.concurrent.Future
import scala.concurrent.duration._

object InteractionDiscovery extends LazyLogging {

  def extractSamePodInteractions(httpClient: Client[IO], localhostPorts: List[Int])
                                (implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[List[InteractionInstanceF[IO]]] = {
    localhostPorts.map(port =>
      extractInteractions(httpClient,
        Uri.unsafeFromString(s"http://localhost:$port")
      )
    )
      .sequence
      .map(_.flatten)
  }

  def extractInterfacesFromDeployedInteraction(httpClient: Client[IO], deployedService: Service)
                                              (implicit contextShift: ContextShift[IO], timer: Timer[IO])
  : IO[List[InteractionInstanceF[IO]]] = {
    val deployedPort = deployedService.spec
      .flatMap(_.ports.find(_.name == "http-api")) // todo this is a convention
      .map(_.port)
      .getOrElse(8080)
    val protocol = /*if(interactionClientTLS.isDefined) "https" else */ "http"
    extractInteractions(httpClient, Uri.unsafeFromString(s"$protocol://${deployedService.name}:$deployedPort/"))
  }

  private def extractInteractions(httpClient: Client[IO], address: Uri)
                                (implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[List[InteractionInstanceF[IO]]] = {
    val client = new RemoteInteractionClient(httpClient, address)

    within(time = 10 minutes, split = 40) { // check every 15 seconds for interfaces for 10 minutes
      // after 10 minutes the failed assertion is propagated, we assume the service is gone and never comes back
      client.interface.map { interfaces =>
        assert(interfaces.nonEmpty);
        interfaces.map(interaction =>
            InteractionInstanceF.build[IO](
              _name = interaction.name,
              _input = interaction.input,
              _run = input => client.runInteraction(interaction.id, input)
            )
          )
      }
    }
  }


  private def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }
    inner(split, time / split)
  }

  /** Creates resource of a ServiceDiscovery module, when acquired a stream of kubernetes services starts and feeds the
   * ServiceDiscovery module to give corresponding InteractionInstances
   * When the resource is released the polling to the Kubernetes API stops.
   *
   * Current hard coded polling periods: 2 seconds
   *
   * @param interactionHttpClient to be used for interaction with the remote interactions
   * @param contextShift          to be used by the streams
   * @param timer                 to be used by the streams
   * @return
   */
  def resource(interactionHttpClient: Client[IO],
               k8s: KubernetesClient,
               localInteractions: LocalInteractions,
               localhostPorts: List[Int],
               podLabelSelector: Option[LabelSelector])(implicit contextShift: ContextShift[IO], timer: Timer[IO], actorSystem: ActorSystem): Resource[IO, InteractionDiscovery] = {

    def watchSource(discovery: InteractionDiscovery): Source[K8SWatchEvent[Service], UniqueKillSwitch] = {
      val watchFilter: ListOptions = ListOptions(labelSelector = podLabelSelector)
      /*, timeoutSeconds = Some(45)*/ // Note, we decided to go for long connections against renewing every 45 seconds due an issue with OpenShift 3.11 not being able to respond to calls with resourceVersion as supposed to be

      // todo how do we ensure that connection on the long poll is not dead?
      def source: Source[K8SWatchEvent[Service], NotUsed] =
        k8s.watchWithOptions[Service](watchFilter, bufsize = Int.MaxValue).mapMaterializedValue(_ => NotUsed)

      RestartSource.withBackoff(RestartSettings(
        minBackoff = 3.seconds,
        maxBackoff = 30.seconds,
        randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
      )) { () =>
        source.mapError { case e =>
          logger.error("Interaction discovery watch stream error: " + e.getMessage, e)
          e
        }
      }.viaMat(KillSwitches.single)(Keep.right)
    }

    def updateSink(interactionDiscovery: InteractionDiscovery): Sink[K8SWatchEvent[Service], Future[Done]] = {
      Sink.foreach[K8SWatchEvent[Service]] { event =>
        interactionDiscovery.update(event).recover { case e =>
          logger.error("Failure when updating the services in the ConfigMap Discovery component", e)
        }.unsafeToFuture()
      }
    }

    Resource.make(for {
      sameJvmInteractions <- localInteractions.instances
      samePodInteractions <- extractSamePodInteractions(interactionHttpClient, localhostPorts)
      discovery = new InteractionDiscovery(
        samePodInteractions ++ sameJvmInteractions,
        interactionHttpClient
      )
      killSwitch <- IO {
        watchSource(discovery).toMat(updateSink(discovery))(Keep.left).run()
      }
    } yield (discovery, killSwitch)) { case (_, hook) => IO(hook.shutdown()) }.map(_._1)
  }
}

final class InteractionDiscovery(val availableInteractions: List[InteractionInstanceF[IO]],
                                  interactionHttpClient: Client[IO])
                                (implicit sync: Sync[IO]) extends LazyLogging {

  val currentlyKnownInteractions: IO[Ref[IO, Set[InteractionInstanceF[IO]]]] = Ref.of[IO, Set[InteractionInstanceF[IO]]](Set.empty)

  import InteractionDiscovery._

  def interactions: InteractionsF[IO] = new InteractionsF[IO] {

    override def instances: IO[Seq[InteractionInstanceF[IO]]] = ???

    override def findImplementation(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[InteractionInstanceF[IO]]] = ???
  }

  def update(event: K8SWatchEvent[Service])(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Unit] =
    event._type match {
      case EventType.ADDED | EventType.MODIFIED =>
        for {
          interactions <- extractInterfacesFromDeployedInteraction(interactionHttpClient, event._object)
          // todo update discovered
        } yield ()
      case EventType.DELETED =>
        removeInteractionsFrom(event._object)
      case EventType.ERROR =>
        IO(logger.error(s"Event type ERROR on service watch for service ${event._object}"))
    }

//  private def updateInteractionsFrom(service: Service)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Unit] =
//    for {
//      address <- extractAddress(service)
//      interfaces <- extractInterfaces(service)
//      client = new RemoteInteractionClient(interactionHttpClient, address)
//      interactions = interfaces.map { interaction =>
//        logger.info(s"Added remote interaction ${interaction.id} ${interaction.name} from $address")
//        interaction.id -> InteractionInstance(
//          name = interaction.name,
//          input = interaction.input,
//          run = input => client.runInteraction(interaction.id, input).unsafeToFuture()
//        )
//      }.toMap
//      _ <- cache.update(_ ++ interactions)
//      _ = logger.info(s"Added interactions: ${interfaces.map(_.name).mkString(", ")}")
//    } yield ()

  private def removeInteractionsFrom(service: Service): IO[Unit] = {
    IO.unit
//    for {
//      interfaces <- extractInterfaces(service)
//      _ <- cache.update(current =>
//        interfaces.foldLeft(current) { case (updated, interaction) => updated - interaction.id })
//      _ = logger.info(s"Removed interactions: ${interfaces.map(_.name).mkString(", ")}")
//    } yield ()
  }

  private def extractAddress(service: Service): IO[Uri] =
    service.spec.map(_.clusterIP) match {
      case Some(address) => IO(Uri.unsafeFromString(address))
      case None => IO.raiseError(new IllegalStateException("'address' key not found in interaction creation contract config map"))
    }
//
//  private def extractInterfaces(service: Service): IO[List[InteractionExecution.Interaction]] = {
//
//    service.data.get("interfaces").map(parse) map {
//      case Right(json) => json.as[List[InteractionExecution.Interaction]].map(interactions =>
//        IO.pure(interactions)
//      ) getOrElse IO.raiseError(new IllegalStateException(s"Can't decode list from $json"))
//      case Left(value) =>
//        IO.raiseError(new IllegalStateException(s"Can't parse config map data: $value"))
//    } getOrElse {
//      IO.raiseError(new IllegalStateException("'interfaces' key not found in interaction creation contract config map"))
//    }
//  }



}
