package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.syntax.traverse._
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client

import java.io.IOException
import scala.concurrent.duration.{DurationInt, FiniteDuration}
import scala.util.Try

object InteractionRegistry extends LazyLogging {

  def resource(managers: InteractionManager[IO]*): Resource[IO, InteractionManager[IO]] =
    Resource.eval[IO, InteractionManager[IO]] {
      IO {
        new TraversingInteractionRegistry {
          override def interactionManagers: List[InteractionManager[IO]] = managers.toList
        }
      }
  }

  def resource(config: Config, actorSystem: ActorSystem): Resource[IO, InteractionManager[IO]] =
    Resource.eval[IO, InteractionManager[IO]] {
      IO {
        val interactionsClass = Try{
          config.getString("baker.interactions.class")
        } getOrElse("com.ing.bakery.baker.LocalInteractions")
        if (interactionsClass != "") {
          Class
            .forName(interactionsClass)
            .getDeclaredConstructor(classOf[Config], classOf[ActorSystem])
            .newInstance(config, actorSystem)
            .asInstanceOf[InteractionManager[IO]]
        } else throw new IllegalArgumentException(s"Class $interactionsClass must extend com.ing.baker.runtime.model.InteractionManager")
      }
    }
}

trait TraversingInteractionRegistry extends InteractionManager[IO] {

  def interactionManagers: List[InteractionManager[IO]]

  // allow, if just one allows
  override lazy val allowSupersetForOutputTypes: Boolean =
    interactionManagers.exists(_.allowSupersetForOutputTypes)

  override def listAll: IO[List[InteractionInstance[IO]]] =
    interactionManagers.traverse(_.listAll).map(_.flatten)

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
