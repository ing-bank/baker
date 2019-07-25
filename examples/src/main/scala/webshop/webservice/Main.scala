package webshop.webservice

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.{Config, ConfigFactory}
import org.http4s.server.blaze.BlazeServerBuilder

object Main extends IOApp {

  val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
  val materializer: Materializer =
    ActorMaterializer()(actorSystem)
  val config: Config =
    ConfigFactory.load()
  val baker: Baker =
    Baker.akkaLocalDefault(actorSystem, materializer)
  import actorSystem.dispatcher

  override def run(args: List[String]): IO[ExitCode] =
    for {
      checkoutRecipeId <- WebShopBaker.initRecipes(baker)
      webShopBaker = new WebShopBaker(baker, checkoutRecipeId)
      app = new CheckoutHttp(webShopBaker)
      status <- BlazeServerBuilder[IO]
        .bindHttp(8080, "localhost")
        .withHttpApp(app.buildHttpService)
        .resource
        .use(_ => IO.never)
        .as(ExitCode.Success)
    } yield status

}
