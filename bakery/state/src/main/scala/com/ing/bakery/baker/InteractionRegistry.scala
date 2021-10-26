package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ConcurrentEffect, ContextShift, IO, Resource, Timer}
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.ing.baker.runtime.defaultinteractions
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.blaze.client.BlazeClientBuilder
import scalax.collection.ChainingOps
import skuber.api.client.KubernetesClient

import java.io.IOException
import scala.concurrent.duration.{DurationInt, FiniteDuration}
import scala.util.Try

object InteractionRegistry extends LazyLogging {

  def resource(config: Config, actorSystem: ActorSystem): Resource[IO, InteractionRegistry] =
    (Try {
      config.getString("baker.interactions.class")
    } toOption)
      .map(Class.forName)
      .getOrElse(classOf[BaseInteractionRegistry])
      .tap(c => logger.info(s"Interaction registry: ${c.getName}"))
      .getDeclaredConstructor(classOf[Config], classOf[ActorSystem])
      .newInstance(config, actorSystem)
      .asInstanceOf[InteractionRegistry]
      .resource
}


/**
  * Registry of interactions, bundles together several interaction managers that provide actual interactions.
  * It also implements InteractionManager[IO] interface, thus for Baker it won't matter if it talks to
  * a single interaction manager or to a registry.
  */
trait InteractionRegistry extends InteractionManager[IO] {
  def resource: Resource[IO, InteractionRegistry]

  def interactionManagers: IO[List[InteractionManager[IO]]]
}

/**
  * Bundles together interactions of all available interaction managers
  */
trait TraversingInteractionRegistry extends InteractionRegistry {
  override def listAll: IO[List[InteractionInstance[IO]]] =
    interactionManagers
      .flatMap(_.traverse(_.listAll).map(_.flatten))
      .flatMap(managed => IO.pure(defaultinteractions.all ++ managed))
}

/**
  * Base implementation of interaction registry
  */
class BaseInteractionRegistry(config: Config, actorSystem: ActorSystem)
  extends TraversingInteractionRegistry
    with LazyLogging {

  implicit val cs: ContextShift[IO] = IO.contextShift(actorSystem.dispatcher)
  implicit val effect: ConcurrentEffect[IO] = IO.ioConcurrentEffect

  // variable state, but changed only once when the resource is started
  protected var managers: List[InteractionManager[IO]] = List.empty[InteractionManager[IO]]

  override def interactionManagers: IO[List[InteractionManager[IO]]] = IO.pure(managers)

  override def resource: Resource[IO, InteractionRegistry] = {
    for {
      client <- BlazeClientBuilder[IO](actorSystem.dispatcher).resource
      interactionManagers <- interactionManagersResource(client)
    } yield {
      managers = interactionManagers
      logger.info(s"Initialised interaction registry with managers: ${managers.map(_.getClass.getName).mkString(",")}")
      this
    }
  }

  protected def interactionManagersResource(client: Client[IO])
  : Resource[IO, List[InteractionManager[IO]]] = for {
    localhost <- new LocalhostInteractions(config, actorSystem, client).resource
    kubernetes <- new KubernetesInteractions(config, actorSystem, client).resource
  } yield {
    List(localhost, kubernetes)
  }
}

/**
  * Method for resilient/retrying discovery of remote interactions
  */
trait RemoteInteractionDiscovery extends LazyLogging {

  def extractInteractions(client: Client[IO], uri: Uri)
                         (implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[List[InteractionInstance[IO]]] = {
    val remoteInteractionClient = new RemoteInteractionClient(client, uri)

    def within[A](giveUpAfter: FiniteDuration, retries: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
      def attempt(count: Int, times: FiniteDuration): IO[A] = {
        if (count < 1) f else f.attempt.flatMap {
          case Left(e) =>
            e match {
              case _: IOException =>
                logger.info(s"Can't connect to interactions @ ${uri.toString}, the container may still be starting...")
              case _ =>
                logger.error(s"Failed to list interactions @ ${uri.toString}", e)
            }
            IO.sleep(times) *> attempt(count - 1, times)
          case Right(a) => IO(a)
        }
      }

      attempt(retries, giveUpAfter / retries)
    }

    within(giveUpAfter = 10 minutes, retries = 40) {
      // check every 15 seconds for interfaces for 10 minutes
      logger.info(s"Extracting interactions @ ${uri.toString}...")
      remoteInteractionClient.interface.map { interfaces =>  {
        if (interfaces.nonEmpty)
          logger.info(s"${uri.toString} provides ${interfaces.size} interactions: ${interfaces.map(_.name).mkString(",")}")
        else
          logger.warn(s"${uri.toString} provides no interactions")
        interfaces.map(interaction => {
          InteractionInstance.build[IO](
            _name = interaction.name,
            _input = interaction.input,
            _output = interaction.output,
            _run = input => remoteInteractionClient.runInteraction(interaction.id, input),
          )
        })
      }}
    }
  }

}
