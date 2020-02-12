package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.model._
import akka.http.scaladsl.unmarshalling.Unmarshal
import akka.stream.Materializer
import com.ing.baker.runtime.serialization.Encryption
import de.heikoseeberger.akkahttpcirce.ErrorAccumulatingCirceSupport
import io.circe.Json

import scala.concurrent.Future

object DashboardClient {

  def apply(hostname: String)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) =
    new DashboardClient(Uri(hostname))
}

class DashboardClient(hostname: Uri)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) extends ErrorAccumulatingCirceSupport {

  import system.dispatcher

  private val root: Path = Path./("api")./("v3")

  private def withPath(path: Path): Uri = hostname.withPath(path)

  def listRecipes: Future[Json] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root / "recipes"))
    Http().singleRequest(request).flatMap(Unmarshal(_).to[Json])
  }

  def getRecipe(recipeId: String): Future[Json] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root / "recipes" / recipeId))
    Http().singleRequest(request).flatMap(Unmarshal(_).to[Json])
  }

  def listInstances(recipeId: String): Future[Json] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root / "recipes" / recipeId / "instances"))
    Http().singleRequest(request).flatMap(Unmarshal(_).to[Json])
  }

  def getRecipeInstance(recipeId: String, recipeInstanceId: String): Future[Json] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root / "recipes" / recipeId / "instances" / recipeInstanceId))
    Http().singleRequest(request).flatMap(Unmarshal(_).to[Json])
  }

  def listRecipeInstanceEvents(recipeId: String, recipeInstanceId: String): Future[Json] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root / "recipes" / recipeId / "instances" / recipeInstanceId / "events"))
    Http().singleRequest(request).flatMap(Unmarshal(_).to[Json])
  }
}
