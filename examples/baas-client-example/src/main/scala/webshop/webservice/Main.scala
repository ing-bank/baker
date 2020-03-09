package webshop.webservice

import java.util.Base64
import java.util.concurrent.Executors

import cats.effect.{ExitCode, IO, IOApp, Resource}
import cats.implicits._
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.serialization.ProtoMap
import com.typesafe.config.ConfigFactory
import org.http4s.Uri
import org.http4s.server.blaze.BlazeServerBuilder

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {

    val compiled = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)
    val protoRecipe: Array[Byte] = ProtoMap.ctxToProto(compiled).toByteArray
    val encode64 = Base64.getEncoder.encode(protoRecipe)

    println(Console.YELLOW + "Recipe base 64:" + Console.RESET)
    println
    println(Console.YELLOW + new String(encode64) + Console.RESET)
    println

    val config =
      ConfigFactory.load()
    val baasHostname =
      config.getString("baas.state-node-hostname")
    val httpPort =
      config.getInt("baas-component.http-api-port")
    val connectionPool =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())
    val mainResource = for {
      baker <- BakerClient.resource(Uri.unsafeFromString(baasHostname), connectionPool)
      checkoutRecipeId  <- Resource.liftF(WebShopBaker.initRecipes(baker))
      _ <- BlazeServerBuilder[IO]
        .bindHttp(httpPort, "0.0.0.0")
        .withHttpApp(new WebShopService(new WebShopBaker(baker, checkoutRecipeId)).build)
        .resource
    } yield ()
    mainResource
      .use(_ => IO.never)
      .as(ExitCode.Success)
  }
}
