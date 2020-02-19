package com.ing.baker.baas.dashboard

import cats.effect.{ContextShift, IO, Resource, Timer}
import io.circe.Json
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.{Status, Uri}

class DashboardClient(client: Resource[IO, Client[IO]], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  private val Root: Uri = hostname / "api" / "v3"

  def ping: IO[Status] =
    client.use(_.statusFromUri(Root / "health"))

  def listRecipes: IO[Json] =
    client.use(_.expect[Json](Root / "recipes"))

  def getRecipe(recipeId: String): IO[Json] =
    client.use(_.expect[Json](Root / "recipes" / recipeId))

  def listInstances(recipeId: String): IO[Json] =
    client.use(_.expect[Json](Root / "recipes" / recipeId / "instances"))

  def getRecipeInstance(recipeId: String, recipeInstanceId: String): IO[Json] =
    client.use(_.expect[Json](Root / "recipes" / recipeId / "instances" / recipeInstanceId))

  def listRecipeInstanceEvents(recipeId: String, recipeInstanceId: String): IO[Json] =
    client.use(_.expect[Json](Root / "recipes" / recipeId / "instances" / recipeInstanceId / "events"))
}
