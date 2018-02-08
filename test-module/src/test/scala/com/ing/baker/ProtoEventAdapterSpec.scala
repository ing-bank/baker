package com.ing.baker

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.ActionType.SieveAction
import com.ing.baker.il.failurestrategy.RetryWithIncrementalBackoff
import com.ing.baker.il.petrinet.Place.IngredientPlace
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, IntermediateTransition, Place}
import com.ing.baker.il.{EventDescriptor, EventOutputTransformer, IngredientDescriptor}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.serialization.{ObjectSerializer, ProtoEventAdapter}
import com.ing.baker.types.{NullValue, PrimitiveType}
import org.scalatest.{FunSuiteLike, Matchers}

import scala.concurrent.duration._

class ProtoEventAdapterSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Matchers  {

  val eventAdapter = new ProtoEventAdapter {
    override val objectSerializer: ObjectSerializer = new ObjectSerializer(system)
  }

  test("should serialize RecipeAdded") {

    val recipe = AllTypeRecipe.recipe
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

    val domainObject = RecipeAdded("recipeId", compiledRecipe)
    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
  }


/*





 */

//  test("should serialize RecipeAdded") {
//
//    val recipe = Examples.open_account.openAccountRecipe
//    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
//
//    val domainObject = RecipeAdded("recipeId", compiledRecipe)
//    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
//  }
//
//  test("should serialize Place") {
//    val domainObject = Place("somePlace", IngredientPlace)
//    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
//  }
//
//  test("should serialize EventTransition") {
//    val ingredients = Seq(IngredientDescriptor("ingredient1", PrimitiveType(classOf[String])), IngredientDescriptor("ingredient2", PrimitiveType(classOf[Int])))
//    val domainObject = EventTransition(EventDescriptor("someEvent", ingredients), maxFiringLimit = Some(3))
//    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
//  }
//
//  test("should serialize IntermediateTransition") {
//    val domainObject = IntermediateTransition("someCustomLabel")
//    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
//  }
//
//  test("should serialize InteractionTransition") {
//    val domainObject = InteractionTransition(
//      eventsToFire = Seq(EventDescriptor("someEvent", Seq(IngredientDescriptor("someIngredient", PrimitiveType(classOf[String]))))),
//      originalEvents = Seq(EventDescriptor("someEvent", Seq(IngredientDescriptor("someIngredient", PrimitiveType(classOf[String]))))),
//      providedIngredientEvent = Some(EventDescriptor("someEvent", Seq(IngredientDescriptor("someIngredient", PrimitiveType(classOf[String]))))),
//      requiredIngredients = Seq(IngredientDescriptor("someIngredient", PrimitiveType(classOf[String]))),
//      interactionName = "someInteraction",
//      originalInteractionName = "someOriginalInteractionName",
//      actionType = SieveAction,
//      predefinedParameters = Map("someIngredient" -> NullValue),
//      maximumInteractionCount = Some(3),
//      failureStrategy = RetryWithIncrementalBackoff(10 seconds, 2.0, 5, Some(24 hours),
//        Some(EventDescriptor("someEvent", Seq(IngredientDescriptor("someIngredient", PrimitiveType(classOf[String])))))
//      ),
//      eventOutputTransformers = Map("oldEventName" -> EventOutputTransformer("newEventName", Map("oldIngredient" -> "newIngredient")))
//    )
//    domainObject shouldBe eventAdapter.toDomain(eventAdapter.toProto(domainObject))
//  }

}