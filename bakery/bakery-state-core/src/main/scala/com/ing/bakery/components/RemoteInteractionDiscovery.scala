package com.ing.bakery.components

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceInput}
import com.ing.baker.types.Type
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri

import java.io.IOException
import scala.concurrent.duration.{DurationInt, FiniteDuration}

/**
 * Method for resilient/retrying discovery of remote interactions
 */
trait RemoteInteractionDiscovery extends LazyLogging {

  def extractInteractions(remoteInteractions: RemoteInteractionClient, uri: Uri): IO[RemoteInteractions] = {

    def within[A](giveUpAfter: FiniteDuration, retries: Int)(f: IO[A]): IO[A] = {
      def attempt(count: Int, times: FiniteDuration): IO[A] = {
        if (count < 1) f else f.attempt.flatMap {
          case Left(e) =>
            e match {
              case _: IOException =>
                logger.info(s"Can't connect to interactions @ ${uri.toString}, the container may still be starting...")
              case _ =>
                logger.warn(s"Failed to list interactions @ ${uri.toString}. The list of available interactions will not be updated.", e)
            }
            IO.sleep(times) *> attempt(count - 1, times)
          case Right(a) => IO(a)
        }
      }

      attempt(retries, giveUpAfter / retries)
    }

    within(giveUpAfter = 10 minutes, retries = 40) {
      // check every 15 seconds for interfaces for 10 minutes
      logger.debug(s"Extracting interactions @ ${uri.toString}...")
      remoteInteractions.interfaces(uri).map { response => {
        val interfaces = response.interactions
        if (interfaces.isEmpty) logger.warn(s"${uri.toString} provides no interactions")
        RemoteInteractions(response.startedAt,
          interfaces.map(interface => {
            new InteractionInstance[IO] {
              override val name: String = interface.name
              override val input: Seq[InteractionInstanceInput] = interface.input
              override val run: Seq[IngredientInstance] => IO[Option[EventInstance]] = _ => IO.pure(Option.empty) //Ignoring the run since the execute does not use it
              override val output: Option[Map[String, Map[String, Type]]] = interface.output
              override def execute(input: Seq[IngredientInstance], metadata: Map[String, String]): IO[Option[EventInstance]] =
                remoteInteractions.execute(uri, interface.id, input, metadata)
            }
          }))
      }
      }
    }
  }
}
