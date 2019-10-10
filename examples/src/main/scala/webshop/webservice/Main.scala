package webshop.webservice

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{ ExitCode, IO, IOApp, Resource }
import cats.implicits._
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.ConfigFactory
import kamon.Kamon
import org.http4s.server.blaze.BlazeServerBuilder
import org.log4s.Logger

object Main extends IOApp {

  Kamon.init()

  case class SystemResources(actorSystem: ActorSystem, baker: Baker, app: WebShopService)

  val logger: Logger = org.log4s.getLogger

  val system: Resource[IO, SystemResources] =
    Resource.make(
      for {
        actorSystem <- IO { ActorSystem("CheckoutService") }
        config <- IO { ConfigFactory.load() }
        baker <- IO { Baker.akka(config, actorSystem) }
        checkoutRecipeId <- WebShopBaker.initRecipes(baker)(timer, actorSystem.dispatcher)
        webShopBaker = new WebShopBaker(baker, checkoutRecipeId)(actorSystem.dispatcher)
        memoryDumpPath = config.getString("service.memory-dump-path")
        app = new WebShopService(webShopBaker, memoryDumpPath)
        resources = SystemResources(actorSystem, baker, app)
      } yield resources
    )(resources =>
      IO(logger.info("Shutting down the Checkout Service...")) *>
        terminateKamon *>
        terminateCluster(resources) *>
        terminateActorSystem(resources)
    )

  def terminateKamon: IO[Unit] =
    IO.fromFuture(IO(Kamon.stopModules()))

  def terminateCluster(resources: SystemResources): IO[Unit] =
    IO {
      val cluster = Cluster(resources.actorSystem)
      cluster.leave(cluster.selfAddress)
    }

  def terminateActorSystem(resources: SystemResources): IO[Unit] =
    IO.fromFuture(IO { resources.actorSystem.terminate() }).void

  override def run(args: List[String]): IO[ExitCode] = {
    system.flatMap { r =>
      BlazeServerBuilder[IO]
        .bindHttp(8080, "0.0.0.0")
        .withHttpApp(r.app.buildHttpService)
        .resource
    }.use(_ => IO.never).as(ExitCode.Success)
  }

}
