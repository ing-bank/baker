package webshop.webservice

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.{Config, ConfigFactory}
import kamon.Kamon
import org.http4s.server.blaze.BlazeServerBuilder

object Main extends IOApp {

  println("Loading Example Service...")
  Kamon.init()
  val actorSystem: ActorSystem =
    ActorSystem("CheckoutService")
  val materializer: Materializer =
    ActorMaterializer()(actorSystem)
  val config: Config =
    ConfigFactory.load()
  val baker: Baker =
    Baker.akka(config, actorSystem, materializer)
  import actorSystem.dispatcher

  override def run(args: List[String]): IO[ExitCode] = {
    for {
      checkoutRecipeId <- WebShopBaker.initRecipes(baker)
      webShopBaker = new WebShopBaker(baker, checkoutRecipeId)
      app = new WebShopService(webShopBaker)
      status <- BlazeServerBuilder[IO]
        .bindHttp(8080, "0.0.0.0")
        .withHttpApp(app.buildHttpService)
        .resource
        .use(_ => IO.never)
        .as(ExitCode.Success)
    } yield status
  }

}
