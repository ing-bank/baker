package com.ing.bakery.clustercontroller

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource}
import cats.implicits._
import com.typesafe.scalalogging.LazyLogging
import skuber.K8SWatchEvent
import skuber.api.client.{EventType, KubernetesClient}

object RecipeController extends LazyLogging {

  def resource(k8s: KubernetesClient)(implicit contextShift: ContextShift[IO], actorSystem: ActorSystem, materializer: Materializer): Resource[IO, Unit] = {

    val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())

    def handleEvent(event: K8SWatchEvent[RecipeResource]): IO[Unit] = {
      for {
        _ <- event._type match {
          case EventType.ADDED =>
            IO {
              println(Console.CYAN + "ADDED" + Console.RESET)
              println(Console.MAGENTA + event._object.decodeRecipe + Console.RESET)
            }
          case EventType.DELETED =>
            IO {
              println(Console.CYAN + "DELETED" + Console.RESET)
              println(Console.MAGENTA + event._object + Console.RESET)
            }
          case EventType.MODIFIED =>
            IO {
              println(Console.CYAN + "MODIFIED" + Console.RESET)
              println(Console.MAGENTA + event._object + Console.RESET)
            }
          case EventType.ERROR =>
            IO(logger.error(s"Event type ERROR on Recipe CRD watch for recipe ${event._object}"))
        }
      } yield ()
    }

    val create = for {
      killSwitch <- IO {
        k8s.watchAllContinuously[RecipeResource]()
          .viaMat(KillSwitches.single)(Keep.right)
          .toMat(Sink.foreachAsync(paralellism)(handleEvent(_).unsafeToFuture()))(Keep.left)
          .run()
      }
    } yield IO(killSwitch.shutdown())

    Resource.make(create)(identity).map(_ => ())
  }

}
