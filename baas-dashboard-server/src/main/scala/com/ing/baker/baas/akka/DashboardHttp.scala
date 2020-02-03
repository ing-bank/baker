package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.StatusCodes
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.stream.Materializer
import com.ing.baker.runtime.scaladsl.Baker
import de.heikoseeberger.akkahttpcirce.{BaseCirceSupport, ErrorAccumulatingCirceSupport}
import io.circe.generic.auto._

import scala.concurrent.Future

object DashboardHttp {

  def run(baker: Baker)(host: String, port: Int)(implicit system: ActorSystem, mat: Materializer): Future[Http.ServerBinding] = {
    import system.dispatcher
    val server = new DashboardHttp(baker)
    println(port)
    Http().bindAndHandle(server.route, host, port)
  }
}

class DashboardHttp(baker: Baker)(implicit system: ActorSystem, mat: Materializer) extends BaseCirceSupport with ErrorAccumulatingCirceSupport {

  import system.dispatcher

  private def route: Route = concat(pathPrefix("api" )(concat(health, listRecipes)), public)

  private def health: Route = pathPrefix("health")(get(complete(StatusCodes.OK)))

  case class RecipeInfo(name: String, recipeId: String, creationTime: Long)

  case class ListRecipesResponse(recipes: List[RecipeInfo])

  private def listRecipes: Route = pathPrefix("recipes")(get(complete(baker.getAllRecipes.map { recipes =>
    ListRecipesResponse(recipes.values.map { info =>
      RecipeInfo(info.compiledRecipe.name, info.compiledRecipe.recipeId, info.recipeCreatedTime)
    }.toList)
  })))

  // /recipes/{recipe-id}/visualize

  private def public: Route = pathPrefix("dashboard") {
    concat(
      getFromResourceDirectory("public"),
      get(getFromResource("public/index.html")))
  }
}
