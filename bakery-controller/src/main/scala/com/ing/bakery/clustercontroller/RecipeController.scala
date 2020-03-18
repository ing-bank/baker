package com.ing.bakery.clustercontroller

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, Sink}
import akka.stream.{KillSwitches, Materializer}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.scalalogging.LazyLogging
import skuber.K8SWatchEvent
import skuber.api.client.{EventType, KubernetesClient}

object RecipeController extends LazyLogging {

  def resource(k8s: KubernetesClient)(implicit contextShift: ContextShift[IO], timer: Timer[IO], actorSystem: ActorSystem, materializer: Materializer): Resource[IO, Unit] = {

    val paralellism = math.max(2, Runtime.getRuntime.availableProcessors())

    def handleEvent(event: K8SWatchEvent[RecipeResource]): IO[Unit] = {
      val ops = new RecipeOps(event._object, k8s)
      println(Console.YELLOW + event._type + " " + event._object.metadata.name + Console.RESET)
      event._type match {
        case EventType.ADDED => ops.createBakeryCluster
        case EventType.DELETED => ops.terminateBakeryCluster
        case EventType.MODIFIED => ops.upgradeBakeryCluster
        case EventType.ERROR => IO(logger.error(s"Event type ERROR on Recipe CRD watch for recipe ${event._object}"))
      }
    }

    val create = for {
      killSwitch <- IO {
        k8s.watchAllContinuously[RecipeResource]()
          .viaMat(KillSwitches.single)(Keep.right)
          .toMat(Sink.foreachAsync(paralellism)(handleEvent(_).unsafeToFuture()))(Keep.left)
          .run()
      }
      _ = sys.addShutdownHook(killSwitch.shutdown())
    } yield IO(killSwitch.shutdown())

    Resource.make(create)(identity).map(_ => ())
  }
}
