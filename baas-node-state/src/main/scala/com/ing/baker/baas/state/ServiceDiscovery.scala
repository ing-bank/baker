package com.ing.baker.baas.state

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
import fs2.Stream
import io.kubernetes.client.openapi.ApiClient
import io.kubernetes.client.openapi.apis.CoreV1Api
import io.kubernetes.client.openapi.models.V1Service
import io.kubernetes.client.util.ClientBuilder
import org.http4s.Uri

import scala.collection.JavaConverters._
import scala.concurrent.duration._
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
    * @param namespace Kubernetes namespace to be queried
    * @param client Kubernetes java client to be used
    * @param contextShift to be used by the streams
    * @param timer to be used by the streams
    * @param blockingEC pool used for the blocking operation of the java library
    * @return
    */
  def resource(connectionPool: ExecutionContext, namespace: String, client: ApiClient = ClientBuilder.cluster.build)(implicit contextShift: ContextShift[IO], timer: Timer[IO], blockingEC: ExecutionContext): Resource[IO, ServiceDiscovery] = {
    val api = new CoreV1Api(client)

    def fetchServices(namespace: String, api: CoreV1Api)(implicit contextShift: ContextShift[IO], blockingEC: ExecutionContext): IO[List[V1Service]] =
      contextShift.evalOn(blockingEC)(IO {
        api.listNamespacedService(namespace, null, null, null, null, null, null, null, null, null)
          .getItems
          .asScala
          .toList
      }).attempt.flatMap {
        case Right(services) =>
          IO.pure(services)
        case Left(e) =>
          IO(logger.warn("Failed to communicate with the Kubernetes service: " + e.getMessage))
          IO.pure(List.empty)
      }

    def getInteractionAddresses(currentServices: List[V1Service]): List[Uri] =
      currentServices
        .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
          .equals("remote-interaction"))
        .map(service => "http://" + service.getMetadata.getName + ":" + service.getSpec.getPorts.asScala.head.getPort)
        .map(Uri.unsafeFromString)

    def getEventListenersAddresses(currentServices: List[V1Service]): List[(String, Uri)] =
      currentServices
        .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
          .equals("remote-event-listener"))
        .map { service =>
          val recipe = service.getMetadata.getLabels.getOrDefault("baker-recipe", "All-Recipes")
          val address = Uri.unsafeFromString("http://" + service.getMetadata.getName + ":" +  + service.getSpec.getPorts.asScala.head.getPort)
          recipe -> address
        }

    def getBakerEventListenersAddresses(currentServices: List[V1Service]): List[Uri] =
      currentServices
        .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
          .equals("remote-baker-event-listener"))
        .map(service => "http://" + service.getMetadata.getName + ":" + service.getSpec.getPorts.asScala.head.getPort)
        .map(Uri.unsafeFromString)

    def buildInteractions(currentServices: List[V1Service]): IO[List[InteractionInstance]] =
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

    def buildRecipeListeners(currentServices: List[V1Service]): Map[RecipeName, List[RecipeListener]] =
      getEventListenersAddresses(currentServices)
        .map { case (recipe, address) => (recipe, RemoteEventListenerClient.resource(address, connectionPool)) }
        .foldLeft(Map.empty[RecipeName, List[RecipeListener]]) { case (acc, (recipeName, client)) =>
          acc + (recipeName -> (client :: acc.getOrElse(recipeName, List.empty)))
        }

    def buildBakerListeners(currentServices: List[V1Service]): List[BakerListener] =
      getBakerEventListenersAddresses(currentServices)
        .map(RemoteBakerEventListenerClient.resource(_, connectionPool))

    val stream = for {
      cacheInteractions <- Stream.eval(Ref.of[IO, List[InteractionInstance]](List.empty))
      cacheRecipeListeners <- Stream.eval(Ref.of[IO, Map[RecipeName, List[RecipeListener]]](Map.empty))
      cacheBakerListeners <- Stream.eval(Ref.of[IO, List[BakerListener]](List.empty))
      service = new ServiceDiscovery(cacheInteractions, cacheRecipeListeners, cacheBakerListeners)
      updateServices = fetchServices(namespace, api)
        .flatMap { currentServices =>
          List(
            buildInteractions(currentServices).flatMap(cacheInteractions.set),
            cacheRecipeListeners.set(buildRecipeListeners(currentServices)),
            cacheBakerListeners.set(buildBakerListeners(currentServices))
          ).parSequence
        }
      updater = Stream.fixedRate(5.seconds).evalMap(_ => updateServices)
      _ <- Stream.eval(updateServices).concurrently(updater)
    } yield service

    stream.compile.resource.lastOrError
  }
}

final class ServiceDiscovery private(
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
