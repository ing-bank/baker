package com.ing.baker.test.recipe

import akka.actor.ActorSystem
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

object WebshopBaker {

  val baker: Baker = AkkaBaker(ConfigFactory.load, ActorSystem.apply("test"))

  baker.addInteractionInstance(InteractionInstance.unsafeFrom(new ReserveItemsInteraction))

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
  val recipeId: String = Await.result(baker.addRecipe(compiledRecipe), 1 seconds)

}
