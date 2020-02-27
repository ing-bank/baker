package webshop.webservice

import akka.actor.ActorSystem
import akka.http.scaladsl.model.Uri
import akka.stream.ActorMaterializer
import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory
import org.http4s.server.blaze.BlazeServerBuilder

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends IOApp {

  case class AppDependencies(actorSystem: ActorSystem, baker: Baker, app: WebShopService, port: Int)

  def dependencies: IO[AppDependencies] = {
    val config = ConfigFactory.load()
    val baasHostname = config.getString("baas.state-node-hostname")
    val httpPort = config.getInt("baas-component.http-api-port")

    implicit val system = ActorSystem("CheckoutService")
    implicit val materializer = ActorMaterializer()
    implicit val encryption = Encryption.from(config)

    val baker = BakerClient(Uri.parseAbsolute(baasHostname))
    sys.addShutdownHook(Await.result(baker.gracefulShutdown(), 20.seconds))

    import system.dispatcher

    for {
      checkoutRecipeId <- WebShopBaker.initRecipes(baker)
      webShopBaker = new WebShopBaker(baker, checkoutRecipeId)
      app = new WebShopService(webShopBaker)
      resources = AppDependencies(system, baker, app, httpPort)
    } yield resources
  }

  override def run(args: List[String]): IO[ExitCode] =
    for {
      deps <- dependencies
      exitCode <- BlazeServerBuilder[IO]
        .bindHttp(deps.port, "0.0.0.0")
        .withHttpApp(deps.app.build)
        .resource
        .use(_ => IO.never)
        .as(ExitCode.Success)
    } yield exitCode

}
