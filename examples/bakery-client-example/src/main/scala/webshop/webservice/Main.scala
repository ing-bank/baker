package webshop.webservice

import java.util.concurrent.Executors

import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.bakery.scaladsl.BakerClient
import com.typesafe.config.ConfigFactory
import org.http4s.Uri
import org.http4s.server.blaze.BlazeServerBuilder

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {

    val compiled = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    val checkoutRecipeId = compiled.recipeId
    /*
    val protoRecipe: Array[Byte] = ProtoMap.ctxToProto(compiled).toByteArray
    val encode64 = Base64.getEncoder.encode(protoRecipe)
     */

    val config =
      ConfigFactory.load()
    val bakeryHostname =
      config.getString("bakery.baker-hostname")
    val httpPort =
      config.getInt("bakery-component.http-api-port")
    val connectionPool: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    val mainResource = for {
      baker <- BakerClient.resource(Uri.unsafeFromString(bakeryHostname), "/api/bakery", connectionPool)
      management <- StateNodeManagementClient.resource(Uri.unsafeFromString(bakeryHostname), connectionPool)
      _ <- BlazeServerBuilder[IO](connectionPool)
        .bindHttp(httpPort, "0.0.0.0")
        .withHttpApp(new WebShopService(new WebShopBaker(baker, checkoutRecipeId), management).build)
        .resource
    } yield ()
    mainResource
      .use(_ => IO.never)
      .as(ExitCode.Success)
  }
}
