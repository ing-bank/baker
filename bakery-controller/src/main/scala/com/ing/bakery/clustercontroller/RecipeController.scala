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
      event._type match {
        case EventType.ADDED => RecipeOps.k8s.createBakeryCluster.run(event._object, k8s)
        case EventType.DELETED => RecipeOps.k8s.terminateBakeryCluster.run(event._object, k8s)
        case EventType.MODIFIED => RecipeOps.k8s.upgradeBakeryCluster.run(event._object, k8s)
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
