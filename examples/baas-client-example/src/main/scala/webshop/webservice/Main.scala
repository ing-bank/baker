package webshop.webservice

import akka.actor.ActorSystem
import akka.http.scaladsl.model.Uri
import akka.stream.ActorMaterializer
import cats.effect.concurrent.Ref
import cats.effect.{ExitCode, IO, IOApp, Resource}
import cats.implicits._
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory
import org.http4s.server.blaze.BlazeServerBuilder
import org.log4s.Logger

object Main extends IOApp {

  case class SystemResources(actorSystem: ActorSystem, baker: Baker, app: WebShopService, port: Int, shuttingDown: Ref[IO, Boolean])

  val logger: Logger = org.log4s.getLogger

  val system: Resource[IO, SystemResources] =
    Resource.make(
      for {
        actorSystem <- IO { ActorSystem("CheckoutService") }
        config <- IO { ConfigFactory.load() }
        materializer = ActorMaterializer()(actorSystem)
        baasHostname = config.getString("baas.state-node-hostname")
        encryption = Encryption.from(config)
        baker <- IO { BakerClient(Uri.parseAbsolute(baasHostname))(actorSystem, materializer, encryption) }
        checkoutRecipeId <- WebShopBaker.initRecipes(baker)(timer, actorSystem.dispatcher)
        sd <- Ref.of[IO, Boolean](false)
        webShopBaker = new WebShopBaker(baker, checkoutRecipeId)(actorSystem.dispatcher)
        httpPort = config.getInt("baas-component.http-api-port")
        app = new WebShopService(webShopBaker)
        resources = SystemResources(actorSystem, baker, app, httpPort, sd)
      } yield resources
    )(resources =>
      IO(logger.info("Shutting down the Checkout Service...")) *>
        terminateActorSystem(resources)
    )

  def terminateActorSystem(resources: SystemResources): IO[Unit] =
    IO.fromFuture(IO { resources.actorSystem.terminate() }).void

  override def run(args: List[String]): IO[ExitCode] = {
    system.flatMap { r =>

      println(Console.GREEN + "Example client app started..." + Console.RESET)
      sys.addShutdownHook(r.baker.gracefulShutdown())

      BlazeServerBuilder[IO]
        .bindHttp(r.port, "0.0.0.0")
        .withHttpApp(r.app.buildHttpService(r.shuttingDown))
        .resource
    }.use(_ => IO.never).as(ExitCode.Success)
  }

}
