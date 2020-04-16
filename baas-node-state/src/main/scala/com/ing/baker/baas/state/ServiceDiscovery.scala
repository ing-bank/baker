package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.internal.InteractionManager
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import skuber._
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._

import scala.concurrent.{ExecutionContext, Future}

/*

REFACTOR: listening at the services is hackish, listening directly to the interaction CRD would be better, although
we need to await for success of deployment, for which a new CRD can be created, so that the BakeryController can
create/delete this new CRD with all the information about the deployed interactions and also creating a contract,
promising that the existence of this CRD ensures the availability of the interactions (then again, with extra generated
data, like the interfaces, names, version etc)

rename crd: Interaction -> InteractionContainer
new crd: InteractionSet

 */

object ServiceDiscovery extends LazyLogging {

  def empty(connectionPool: ExecutionContext): IO[ServiceDiscovery] =
    Ref.of[IO, List[InteractionInstance]](List.empty).map(new ServiceDiscovery(_, connectionPool))


  /** Creates resource of a ServiceDiscovery module, when acquired a stream of kubernetes services starts and feeds the
    * ServiceDiscovery module to give corresponding InteractionInstances
    * When the resource is released the polling to the Kubernetes API stops.
    *
    * Current hard coded polling periods: 2 seconds
    *
    * @param connectionPool to be used for client connections
    * @param contextShift to be used by the streams
    * @param timer to be used by the streams
    * @return
    */
  def resource(connectionPool: ExecutionContext, k8s: KubernetesClient)(implicit contextShift: ContextShift[IO], timer: Timer[IO], actorSystem: ActorSystem, materializer: Materializer): Resource[IO, ServiceDiscovery] = {

    val createServiceDiscovery =
      for {
        serviceDiscovery <- ServiceDiscovery.empty(connectionPool)
        sink = Sink
          .foreach[Option[K8SWatchEvent[Service]]] {
            case Some(event) =>
              serviceDiscovery.update(event).recover { case e =>
                println(Console.RED + e + Console.RESET)
                logger.error("Failure when updating the services in the Service Discovery component", e)
              }.unsafeToFuture()
            case None =>
              Future.successful(Unit)
          }
        killSwitch <- IO {
          k8s.watchAllContinuously[Service]()
            .map(Some(_))
            .recover {
              case e =>
                println(Console.RED + e + Console.RESET)
                None
            }
            .viaMat(KillSwitches.single)(Keep.right)
            .toMat(sink)(Keep.left)
            .run()
        }
      } yield (serviceDiscovery, killSwitch)

    Resource.make(createServiceDiscovery)(s => IO(s._2.shutdown())).map(_._1)
  }
}

final class ServiceDiscovery private(
  cacheInteractions: Ref[IO, List[InteractionInstance]],
  connectionPool: ExecutionContext
) extends LazyLogging {

  def get: IO[List[InteractionInstance]] =
    cacheInteractions.get

  def update(event: K8SWatchEvent[Service])(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[Unit] = {
    println(Console.YELLOW + event + Console.RESET)
    for {
      _ <- event._type match {
        case EventType.ADDED =>
          filterServiceAndGetInteractionAddress(event._object)
            .map(buildInteractionInstances(_)
              .flatMap(newInteractions => cacheInteractions.update(_ ++ newInteractions)))
            .getOrElse(IO.unit)
        //currentServices.updateAndGet(_ + (event._object.metadata.uid -> event._object))
        case EventType.DELETED =>
          // TODO There can be several interactions in a service, that is why we need to request the interface again
          // to delete all interactions in the cache related to the service, but by this moment, the interface is unreachable,
          //  (remember as well: there might be same name with different interfaces)
          // TODO an improvement might be to publish all interaction names with base64 interfaces in the tags of the service
          IO.unit
        case EventType.MODIFIED =>
          IO.unit
        //currentServices.updateAndGet(_ + (event._object.metadata.uid -> event._object))
        case EventType.ERROR =>
          IO(logger.error(s"Event type ERROR on service watch for service ${event._object}"))
      }
      current <- cacheInteractions.get
      _ = println("[INFO] Current Interactions: " + current.map(_.name).mkString(", "))
    } yield ()
  }

  def buildInteractionManager: InteractionManager =
    new InteractionManager {
      override def addImplementation(interaction: InteractionInstance): Future[Unit] =
        Future.failed(new IllegalStateException("Adding implementation instances is not supported on a Bakery cluster."))
      override def getImplementation(interaction: InteractionTransition): Future[Option[InteractionInstance]] =
        cacheInteractions.get.map(_.find(isCompatibleImplementation(interaction, _))).unsafeToFuture()
    }

  private def filterServiceAndGetInteractionAddress(service: Service): Option[Uri] = {
    for {
      componentLabel <- service.metadata.labels.get("baas-component")
      _ <- if(componentLabel == "remote-interaction") Some(()) else None
      port = service.spec
        .flatMap(_.ports.find(_.name == "http-api"))
        .map(_.port.toString)
        .getOrElse("8080")
    } yield Uri.unsafeFromString("http://" + service.metadata.name + ":" + port)
  }

  private def buildInteractionInstances(interactionAddress: Uri)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[List[InteractionInstance]] = {
    val clientR = RemoteInteractionClient.resource(interactionAddress, connectionPool)
    clientR.use { client =>
      for {
        interface <- client.interface.attempt
        _ = println(s"GOT INTERFACES: $interface")
        interactionsOpt = interface match {
          case Right(interfaces) =>
            interfaces.map { i =>
              InteractionInstance(
                name = i.name,
                input = i.interface,
                run = input => clientR.use(_.runInteraction(i.id, input)).unsafeToFuture()
              )
            }
          case Left(e) =>
            println("[ERROR] FAILED TO ADD INTERACTION: " + e.getMessage)
            e.printStackTrace()
            List.empty
        }
      } yield interactionsOpt
    }
  }
}
