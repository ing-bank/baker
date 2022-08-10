package webshop.webservice

import cats.effect.{IO, Resource}
import org.http4s.Method._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

object StateNodeManagementClient {

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
    * the resulting `IO` is run, each time using the common connection pool.
    */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit timer: Temporal[IO]): Resource[IO, StateNodeManagementClient] =
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new StateNodeManagementClient(_, hostname))
}

final class StateNodeManagementClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Temporal[IO]) {

  def knownRecipes: IO[String] = {
    val request = GET(hostname / "api" / "bakery" / "app" / "recipes")
    client.expect[String](request)//.map { _.split(",").toList }
  }

  def knownInteractionNames: IO[List[String]] = {
    val request = GET(hostname / "api" / "bakery" / "app" / "interactions")
    client.expect[String](request).map { _.split(",").toList }
  }

  def getEvents(recipeInstanceId: String): IO[List[String]] = {
    val request = GET(hostname / "api" / "bakery" / "instances" / recipeInstanceId / "events")
    client.expect[String](request).map(_.split(",").toList)
  }

  def getIngredients(recipeInstanceId: String): IO[List[String]] = {
    val request = GET(hostname / "api" / "bakery" / "instances" / recipeInstanceId / "ingredients")
    client.expect[String](request).map(_.split(",").toList)
  }
}
