package com.ing.baker

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.serialization.{ObjectSerializer, ProtoEventAdapter}
import org.scalatest.{FunSuiteLike, Matchers}

class ProtoEventAdapterSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Matchers  {

  val eventAdapter = new ProtoEventAdapter {
    override val objectSerializer: ObjectSerializer = new ObjectSerializer(system)
  }

  test("should serialize AllTypeRecipe") {
    val recipe = AllTypeRecipe.recipe
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    val domainObject = RecipeAdded("recipeId", compiledRecipe)
    val newDomainObject = eventAdapter.toDomainType[RecipeAdded](eventAdapter.toProto(domainObject))

    domainObject shouldBe newDomainObject
  }

}