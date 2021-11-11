package com.ing.baker.test.recipe

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}

import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

object WebshopBaker {

  implicit val cs: ContextShift[IO] = IO.contextShift(global)

  implicit val timer: Timer[IO] = IO.timer(global)

  val baker: Baker = AkkaBaker.localDefault(ActorSystem.apply,
    CachingInteractionManager(InteractionInstance.unsafeFrom(new ReserveItems)))

  val javaBaker: javadsl.Baker = AkkaBaker.javaOther(baker)

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)

  val recipeId: String = Await.result(baker.addRecipe(compiledRecipe, validate = true), 10 seconds)
}
