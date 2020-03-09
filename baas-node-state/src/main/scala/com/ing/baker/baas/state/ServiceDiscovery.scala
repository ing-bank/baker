package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.baas.bakerlistener.RemoteBakerEventListenerClient
import com.ing.baker.baas.interaction.RemoteInteractionClient
import com.ing.baker.baas.recipelistener.RemoteEventListenerClient
import com.ing.baker.baas.state.ServiceDiscovery.{BakerListener, RecipeListener, RecipeName}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.internal.InteractionManager
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import skuber._
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._

import scala.concurrent.{ExecutionContext, Future}

object ServiceDiscovery extends LazyLogging {

  private[state] type RecipeName = String

  private[state] type RecipeListener = Resource[IO, RemoteEventListenerClient]

  private[state] type BakerListener = Resource[IO, RemoteBakerEventListenerClient]

  /** Creates resource of a ServiceDiscovery module, when acquired a stream of kubernetes services starts and feeds the
    * ServiceDiscovery module to give corresponding InteractionInstances and clients to the event listeners.
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

    def getHttpServicePortOrDefault(service: Service): String = {
      for {
        spec <- service.spec
        portNumber <- spec.ports.find(_.name == "http-api")
      } yield portNumber.port.toString
    }.getOrElse("8080")

    def getInteractionAddresses(currentServices: List[Service]): List[Uri] =
      currentServices
        .filter(_.metadata.labels.getOrElse("baas-component", "Wrong")
          .equals("remote-interaction"))
        .map(service => "http://" + service.metadata.name + ":" + getHttpServicePortOrDefault(service))
        .map(Uri.unsafeFromString)

    def getEventListenersAddresses(currentServices: List[Service]): List[(String, Uri)] =
      currentServices
        .filter(_.metadata.labels.getOrElse("baas-component", "Wrong")
          .equals("remote-event-listener"))
        .map { service =>
          val recipe = service.metadata.labels.getOrElse("baker-recipe", "All-Recipes")
          val address = Uri.unsafeFromString("http://" + service.metadata.name + ":" + getHttpServicePortOrDefault(service))
          recipe -> address
        }

    def getBakerEventListenersAddresses(currentServices: List[Service]): List[Uri] =
      currentServices
        .filter(_.metadata.labels.getOrElse("baas-component", "Wrong")
          .equals("remote-baker-event-listener"))
        .map(service => "http://" + service.metadata.name + ":" + getHttpServicePortOrDefault(service))
        .map(Uri.unsafeFromString)

    def buildInteractions(currentServices: List[Service]): IO[List[InteractionInstance]] =
      getInteractionAddresses(currentServices)
        .map(RemoteInteractionClient.resource(_, connectionPool))
        .parTraverse[IO, Option[InteractionInstance]](buildInteractionInstance)
        .map(_.flatten)

    def buildInteractionInstance(resource: Resource[IO, RemoteInteractionClient]): IO[Option[InteractionInstance]] =
      resource.use { client =>
        for {
          interface <- client.interface.attempt
          interactionsOpt = interface match {
            case Right((name, types)) => Some(InteractionInstance(
              name = name,
              input = types,
              run = input => resource.use(_.runInteraction(input)).unsafeToFuture()
            ))
            case Left(_) => None
          }
        } yield interactionsOpt
      }

    def buildRecipeListeners(currentServices: List[Service]): Map[RecipeName, List[RecipeListener]] =
      getEventListenersAddresses(currentServices)
        .map { case (recipe, address) => (recipe, RemoteEventListenerClient.resource(address, connectionPool)) }
        .foldLeft(Map.empty[RecipeName, List[RecipeListener]]) { case (acc, (recipeName, client)) =>
          acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty)))
        }

    def buildBakerListeners(currentServices: List[Service]): List[BakerListener] =
      getBakerEventListenersAddresses(currentServices)
        .map(RemoteBakerEventListenerClient.resource(_, connectionPool))

    def updateServicesWith(
      currentServices: Ref[IO, List[Service]],
      cacheInteractions: Ref[IO, List[InteractionInstance]],
      cacheRecipeListeners: Ref[IO, Map[RecipeName, List[RecipeListener]]],
      cacheBakerListeners: Ref[IO, List[BakerListener]]
    )(event: K8SWatchEvent[Service]): IO[Unit] = {
      for {
        services <- event._type match {
          case EventType.ADDED =>
            currentServices.updateAndGet(event._object :: _)
          case EventType.DELETED =>
            currentServices.updateAndGet(_.filterNot(_ == event._object))
          case EventType.MODIFIED =>
            currentServices.updateAndGet(_.map(service => if (service.metadata.uid == event._object.metadata.uid) event._object else service))
          case EventType.ERROR =>
            IO(logger.error(s"Event type ERROR on service watch for service ${event._object}")) *> currentServices.get
        }
        _ <- List(
          buildInteractions(services).flatMap(cacheInteractions.set),
          cacheRecipeListeners.set(buildRecipeListeners(services)),
          cacheBakerListeners.set(buildBakerListeners(services))
        ).parSequence
      } yield ()
    }

    val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())
    
    val createServiceDiscovery = for {
      currentServices <- Ref.of[IO, List[Service]](List.empty)
      cacheInteractions <- Ref.of[IO, List[InteractionInstance]](List.empty)
      cacheRecipeListeners <- Ref.of[IO, Map[RecipeName, List[RecipeListener]]](Map.empty)
      cacheBakerListeners <- Ref.of[IO, List[BakerListener]](List.empty)
      service = new ServiceDiscovery(cacheInteractions, cacheRecipeListeners, cacheBakerListeners)
      updateServices = updateServicesWith(currentServices, cacheInteractions, cacheRecipeListeners, cacheBakerListeners) _
      killSwitch <- IO {
        k8s.watchAllContinuously[Service]()
          .viaMat(KillSwitches.single)(Keep.right)
          .toMat(Sink.foreachAsync(paralellism)(updateServices(_).unsafeToFuture()))(Keep.left)
          .run()
      }
    } yield (service, killSwitch)

    Resource.make(createServiceDiscovery)(s => IO(s._2.shutdown())).map(_._1)
  }
}

case class ServiceDiscovery private(
  cacheInteractions: Ref[IO, List[InteractionInstance]],
  cacheRecipeListeners: Ref[IO, Map[RecipeName, List[RecipeListener]]],
  cacheBakerListeners: Ref[IO, List[BakerListener]]
) {

  def plugBakerEventListeners(baker: Baker): IO[Unit] = IO {
    baker.registerBakerEventListener { event =>
      cacheBakerListeners.get.map { listeners =>
        listeners.foreach(_.use(_.fireEvent(event)).unsafeRunAsyncAndForget())
      }.unsafeRunAsyncAndForget()
    }
    baker.registerEventListener { (metadata, event) =>
      cacheRecipeListeners.get.map { listeners =>
        listeners.get(metadata.recipeName).foreach(_.foreach(_.use(_.fireEvent(metadata, event)).unsafeRunAsyncAndForget()))
        listeners.get("All-Recipes").foreach(_.foreach(_.use(_.fireEvent(metadata, event)).unsafeRunAsyncAndForget()))
      }.unsafeRunAsyncAndForget()
    }
  }

  def buildInteractionManager: InteractionManager =
    new InteractionManager {
      override def addImplementation(interaction: InteractionInstance): Future[Unit] =
        Future.failed(new IllegalStateException("Adding implmentation instances is not supported on a Bakery cluster."))
      override def getImplementation(interaction: InteractionTransition): Future[Option[InteractionInstance]] =
        cacheInteractions.get.map(_.find(isCompatibleImplementation(interaction, _))).unsafeToFuture()
    }
}
