package com.ing.baker

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.il.petrinet.{EventTransition, IntermediateTransition, Place}
import com.ing.baker.il.petrinet.Place.IngredientPlace
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.serialization.{ObjectSerializer, ProtoEventAdapter}
import com.ing.baker.types.PrimitiveType
import org.scalatest.{FunSuiteLike, Matchers}

class ProtoEventAdapterSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Matchers  {

  val eventAdapter = new ProtoEventAdapter {
    override val objectSerializer: ObjectSerializer = new ObjectSerializer(system)
  }

  test("should serialize RecipeAdded") {

    val recipe = Examples.open_account.openAccountRecipe
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    val domainObject = RecipeAdded("recipeId", compiledRecipe)
    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
  }

  test("should serialize Place") {
    val domainObject = Place("somePlace", IngredientPlace)
    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
  }

  test("should serialize EventTransition") {
    val ingredients = Seq(IngredientDescriptor("ingredient1", PrimitiveType(classOf[String])), IngredientDescriptor("ingredient2", PrimitiveType(classOf[Int])))
    val domainObject = EventTransition(EventDescriptor("someEvent", ingredients), maxFiringLimit = Some(3))
    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
  }

  test("should serialize IntermediateTransition") {
    val domainObject = IntermediateTransition("someCustomLabel")
    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
  }

}