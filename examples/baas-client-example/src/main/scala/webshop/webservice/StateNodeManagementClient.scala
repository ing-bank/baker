package webshop.webservice

import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s.Method._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._

import scala.concurrent.ExecutionContext

object StateNodeManagementClient {

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
    * the resulting `IO` is run, each time using the common connection pool.
    */
  def resource(hostname: Uri, pool: ExecutionContext)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, StateNodeManagementClient] =
    BlazeClientBuilder[IO](pool)
      .resource
      .map(new StateNodeManagementClient(_, hostname))
}

final class StateNodeManagementClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def knownInteractionNames: IO[List[String]] = {
    val request = GET(hostname / "management" / "interaction")
    client.expect[String](request).map { i =>
      println(i)
      i.split(",").toList
    }
  }

  def getEvents(recipeInstanceId: String): IO[List[String]] = {
    val request = GET(hostname / "recipe-instance" / recipeInstanceId / "events")
    client.expect[String](request).map(_.split(",").toList)
  }

  def getIngredients(recipeInstanceId: String): IO[List[String]] = {
    val request = GET(hostname / "recipe-instance" / recipeInstanceId / "ingredients")
    client.expect[String](request).map(_.split(",").toList)
  }
}
