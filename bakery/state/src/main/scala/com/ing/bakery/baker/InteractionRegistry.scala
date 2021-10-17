package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.concurrent.Ref
import cats.effect.{ConcurrentEffect, ContextShift, IO, Resource, Timer}
import cats.syntax.traverse._
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder

import java.io.IOException
import scala.concurrent.duration.{DurationInt, FiniteDuration}
import scala.util.Try

object InteractionRegistry extends LazyLogging {

  def resource(config: Config, actorSystem: ActorSystem): Resource[IO, InteractionRegistry] =
    (Try {
      config.getString("baker.interactions.class")
    } toOption)
      .map(Class.forName)
      .getOrElse(classOf[DefaultInteractionRegistry])
      .getDeclaredConstructor(classOf[Config], classOf[ActorSystem])
      .newInstance(config, actorSystem)
      .asInstanceOf[InteractionRegistry]
      .resource
}


trait InteractionRegistry extends InteractionManager[IO] {

  def resource: Resource[IO, InteractionRegistry]

  def interactionManagers: IO[List[InteractionManager[IO]]]

}

trait TraversingInteractionRegistry extends InteractionRegistry {

  override def listAll: IO[List[InteractionInstance[IO]]] =
    interactionManagers.flatMap(_.traverse(_.listAll).map(_.flatten))

}


class DefaultInteractionRegistry(config: Config, actorSystem: ActorSystem) extends TraversingInteractionRegistry with LazyLogging {

  private val managers: IO[Ref[IO, List[InteractionManager[IO]]]] =
    Ref.of[IO, List[InteractionManager[IO]]](List.empty)

  override def interactionManagers: IO[List[InteractionManager[IO]]] = for {
    managersRef <- managers
    managers <- managersRef.get
  } yield managers

  override def resource: Resource[IO, InteractionRegistry] = {
    implicit val cs: ContextShift[IO] = IO.contextShift(actorSystem.dispatcher)
    implicit val effect: ConcurrentEffect[IO] = IO.ioConcurrentEffect
    for {
      client <- BlazeClientBuilder[IO](actorSystem.dispatcher).resource
      managersRef <- Resource.eval(managers)
      _ <- Resource.eval(managersRef.set(List(
        new LocalhostInteractions(config, actorSystem, client),
        new K8sInteractions(config, actorSystem, client, skuber.k8sInit(actorSystem))
      )))
    } yield this
  }

}

trait RemoteInteractionDiscovery extends LazyLogging {

  def extractInteractions(client: Client[IO], address: Uri)
                         (implicit contextShift: ContextShift[IO], timer: Timer[IO]): IO[List[InteractionInstance[IO]]] = {
    val remoteInteractionClient = new RemoteInteractionClient(client, address)

    def within[A](giveUpAfter: FiniteDuration, retries: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
      def attempt(count: Int, times: FiniteDuration): IO[A] = {
        if (count < 1) f else f.attempt.flatMap {
          case Left(e) =>
            e match {
              case _: IOException =>
                logger.info(s"Can't connect to interactions @ ${address.toString}, the container may still be starting...")
              case _ =>
                logger.error(s"Failed to list interactions @ ${address.toString}", e)
            }
            IO.sleep(times) *> attempt(count - 1, times)
          case Right(a) => IO(a)
        }
      }

      attempt(retries, giveUpAfter / retries)
    }

    within(giveUpAfter = 10 minutes, retries = 40) {
      // check every 15 seconds for interfaces for 10 minutes
      logger.info(s"Extracting interactions @ ${address.toString}")
      remoteInteractionClient.interface.map { interfaces =>
        assert(interfaces.nonEmpty)
        logger.info(s"Loaded ${interfaces.size} interactions: ${interfaces.map(_.name).mkString(",")}")
        interfaces.map(interaction => {
          InteractionInstance.build[IO](
            _name = interaction.name,
            _input = interaction.input,
            _output = interaction.output,
            _run = input => remoteInteractionClient.runInteraction(interaction.id, input),
          )
        })
      }
    }
  }

}
