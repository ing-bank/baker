package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source}
import akka.stream.{KillSwitches, Materializer, RestartSettings, UniqueKillSwitch}
import akka.{Done, NotUsed}
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.internal.InteractionManager
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.interaction.RemoteInteractionClient
import com.ing.bakery.protocol.InteractionExecution
import com.typesafe.scalalogging.LazyLogging
import io.circe.parser._
import org.http4s.Uri
import org.http4s.client.Client
import skuber._
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._

import scala.concurrent.Future
import scala.concurrent.duration._

object ServiceDiscovery extends LazyLogging {

  def empty(httpClient: Client[IO], scope: String): IO[ServiceDiscovery] =
    Ref.of[IO, Map[String, InteractionInstance]](Map.empty).map(new ServiceDiscovery(_, httpClient, scope))

  /** Creates resource of a ServiceDiscovery module, when acquired a stream of kubernetes services starts and feeds the
    * ServiceDiscovery module to give corresponding InteractionInstances
    * When the resource is released the polling to the Kubernetes API stops.
    *
    * Current hard coded polling periods: 2 seconds
    *
    * @param interactionHttpClient to be used for interaction with the remote interactions
    * @param contextShift to be used by the streams
    * @param timer to be used by the streams
    * @return
    */
  def resource(interactionHttpClient: Client[IO], k8s: KubernetesClient, scope: String)(implicit contextShift: ContextShift[IO], timer: Timer[IO], actorSystem: ActorSystem, materializer: Materializer): Resource[IO, ServiceDiscovery] = {

    def watchSource(serviceDiscovery: ServiceDiscovery): Source[K8SWatchEvent[ConfigMap], UniqueKillSwitch] = {
      val watchFilter: ListOptions = {
        val labelSelector = LabelSelector(
          List(
            Some(LabelSelector.IsEqualRequirement("bakery-manifest", "interactions")),
            if (serviceDiscovery.scope == "*") None
            else Some(LabelSelector.InRequirement("scope", serviceDiscovery.scope.split(",").toList))
          ).flatten: _*
        )
        ListOptions(labelSelector = Some(labelSelector)/*, timeoutSeconds = Some(45)*/) // Note, we decided to go for long connections against renewing every 45 seconds due an issue with OpenShift 3.11 not being able to respond to calls with resourceVersion as supposed to be
      }

      def source: Source[K8SWatchEvent[ConfigMap], NotUsed] =
        k8s.watchWithOptions[ConfigMap](watchFilter, bufsize = Int.MaxValue).mapMaterializedValue(_ => NotUsed)
      RestartSource.withBackoff(RestartSettings(
        minBackoff = 3.seconds,
        maxBackoff = 30.seconds,
        randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
      )) { () =>
        source.mapError { case e =>
          logger.error("Error on the service discovery watch stream: " + e.getMessage, e)
          e
        }
      }.viaMat(KillSwitches.single)(Keep.right)
    }

    def updateSink(serviceDiscovery: ServiceDiscovery): Sink[K8SWatchEvent[ConfigMap], Future[Done]] = {
      Sink.foreach[K8SWatchEvent[ConfigMap]] { event =>
          serviceDiscovery.update(event).recover { case e =>
            logger.error("Failure when updating the services in the ConfigMap Discovery component", e)
          }.unsafeToFuture()
      }
    }

    val createServiceDiscovery: IO[(ServiceDiscovery, UniqueKillSwitch)] =
      for {
        serviceDiscovery <- ServiceDiscovery.empty(interactionHttpClient, scope)
        killSwitch <- IO { watchSource(serviceDiscovery).toMat(updateSink(serviceDiscovery))(Keep.left).run() }
      } yield (serviceDiscovery, killSwitch)

    Resource.make(createServiceDiscovery) { case (_, hook) => IO(hook.shutdown()) }.map(_._1)
  }
}

final class ServiceDiscovery private(
  cacheInteractions: Ref[IO, Map[String, InteractionInstance]],
  interactionHttpClient: Client[IO],
  val scope: String
) extends LazyLogging {

  def get: IO[List[InteractionInstance]] =
    cacheInteractions.get.map(_.values.toList)

  def update(event: K8SWatchEvent[ConfigMap])(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Unit] =
    event._type match {
      case EventType.ADDED =>
        addInteractionInstancesFrom(event._object)
      case EventType.DELETED =>
        removeInteractionInstancesFrom(event._object)
      case EventType.MODIFIED =>
        IO.unit
      case EventType.ERROR =>
        IO(logger.error(s"Event type ERROR on service watch for service ${event._object}"))
    }

  def buildInteractionManager: InteractionManager =
    new InteractionManager {

      override def listAllImplementations: Future[List[InteractionInstance]] =
        cacheInteractions.get.map(_.values.toList).unsafeToFuture()

      override def addImplementation(interaction: InteractionInstance): Future[Unit] =
        Future.failed(new IllegalStateException("Adding implementation instances is not supported on a Bakery cluster."))
      override def getImplementation(interaction: InteractionTransition): Future[Option[InteractionInstance]] =
        cacheInteractions.get.map(_.values.find(isCompatibleImplementation(interaction, _))).unsafeToFuture()
    }

  private def addInteractionInstancesFrom(contract: ConfigMap)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Unit] =
    for {
      address <- extractAddress(contract)
      interfaces <- extractInterfaces(contract)
      client = new RemoteInteractionClient(interactionHttpClient, address)
      interactions = interfaces.map { interaction =>
        interaction.id -> InteractionInstance(
          name = interaction.name,
          input = interaction.input,
          run = input => client.runInteraction(interaction.id, input).unsafeToFuture()
        )
      }.toMap
      _ <- cacheInteractions.update(_ ++ interactions)
      _ = logger.info(s"Added interactions: ${interfaces.map(_.name).mkString(", ")}")
    } yield ()

  private def removeInteractionInstancesFrom(contract: ConfigMap): IO[Unit] = {
    for {
      interfaces <- extractInterfaces(contract)
      _ <- cacheInteractions.update(current =>
        interfaces.foldLeft(current) { case (updated, interaction) => updated - interaction.id })
      _ = logger.info(s"Removed interactions: ${interfaces.map(_.name).mkString(", ")}")
    } yield ()
  }

  private def extractAddress(contract: ConfigMap): IO[Uri] =
    contract.data.get("address") match {
      case Some(address) => IO(Uri.unsafeFromString(address))
      case None => IO.raiseError(new IllegalStateException("'address' key not found in interaction creation contract config map"))
    }

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  private def extractInterfaces(contract: ConfigMap): IO[List[InteractionExecution.Interaction]] = {
    contract.data.get("interfaces").map(parse) map {
      case Right(json) => json.as[List[InteractionExecution.Interaction]].map(interactions =>
        IO.pure(interactions)
      ) getOrElse IO.raiseError(new IllegalStateException(s"Can't decode list from $json"))
      case Left(value) =>
        IO.raiseError(new IllegalStateException(s"Can't parse config map data: $value"))
    } getOrElse {
      IO.raiseError(new IllegalStateException("'interfaces' key not found in interaction creation contract config map"))
    }
  }

}
