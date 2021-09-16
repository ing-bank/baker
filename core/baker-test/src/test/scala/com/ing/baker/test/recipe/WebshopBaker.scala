package com.ing.baker.test.recipe

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.akka.internal.CachedInteractionManager
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object WebshopBaker {

  implicit val cs: ContextShift[IO] = IO.contextShift(global)
  implicit val timer: Timer[IO] = IO.timer(global)

  val baker: Baker = AkkaBaker(ConfigFactory.load, ActorSystem.apply("for-scala-tests"),
    CachedInteractionManager(InteractionInstance.unsafeFrom(new ReserveItemsInteraction)))

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
  val recipeId: String = Await.result(baker.addRecipe(compiledRecipe, validate = true), 10 seconds)
}
