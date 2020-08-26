package webshop.webservice

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.concurrent.Ref
import cats.effect.{ExitCode, IO, IOApp, Resource, SyncIO}
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.ConfigFactory
import kamon.Kamon
import org.http4s.server.blaze.BlazeServerBuilder
import org.log4s.Logger

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  case class SystemResources(actorSystem: ActorSystem, baker: Baker, app: WebShopService, port: Int, shuttingDown: Ref[IO, Boolean])

  val logger: Logger = org.log4s.getLogger

  val system: Resource[IO, SystemResources] =
    Resource.make(
      for {
        actorSystem <- IO { ActorSystem("CheckoutService") }
        config <- IO { ConfigFactory.load() }
        baker <- IO { AkkaBaker(config, actorSystem) }
        checkoutRecipeId <- WebShopBaker.initRecipes(baker)(timer, actorSystem.dispatcher)
        sd <- Ref.of[IO, Boolean](false)
        webShopBaker = new WebShopBaker(baker, checkoutRecipeId)(actorSystem.dispatcher)
        memoryDumpPath = config.getString("service.memory-dump-path")
        httpPort = config.getInt("bakery-component.http-api-port")
        app = new WebShopService(webShopBaker, memoryDumpPath)
        resources = SystemResources(actorSystem, baker, app, httpPort, sd)
      } yield resources
    )(resources =>
      IO(logger.info("Shutting down the Checkout Service...")) *>
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

      sys.addShutdownHook(r.baker.gracefulShutdown())

      BlazeServerBuilder[IO](ExecutionContext.global)
        .bindHttp(r.port, "0.0.0.0")
        .withHttpApp(r.app.buildHttpService(r.shuttingDown))
        .resource
    }.use(_ => IO.never).as(ExitCode.Success)
  }

}
