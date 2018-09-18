package com.ing.baker

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.serialization.{ObjectSerializer, ProtoEventAdapterImpl}
import org.scalatest.{FunSuiteLike, Matchers}

@deprecated("marked deprecated because of -XFatal-Warnings and deprecated sieves", "1.4.0")
class ProtoEventAdapterSpec extends TestKit(ActorSystem("ProtoEventAdapterSpec")) with FunSuiteLike with Matchers  {

  val eventAdapter = new ProtoEventAdapterImpl(new ObjectSerializer(system))

  test("should serialize AllTypeRecipe") {
    val recipe = AllTypeRecipe.recipe
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    val domainObject = RecipeAdded("recipeId", compiledRecipe)
    val newDomainObject = eventAdapter.toDomain[RecipeAdded](eventAdapter.toProtoMessage(domainObject))

    domainObject shouldBe newDomainObject
  }
}