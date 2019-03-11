package com.ing.baker.runtime.actortyped.serialization

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import org.scalacheck.Prop.forAll
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalacheck._
import org.scalatest.FunSuiteLike
import org.scalatest.prop.Checkers
import com.ing.baker.pbt.RecipePropertiesSpec.recipeGen
import com.ing.baker.runtime.actortyped.recipe_manager.RecipeManagerTyped.RecipeAdded

class SerializationSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Checkers {

  val serializer: BakerTypedProtobufSerializer = SerializationExtension.get(system).serializerByIdentity(103).asInstanceOf[BakerTypedProtobufSerializer]

  val recipeAddedGen: Gen[RecipeAdded] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeAdded(recipe, timestamp)

  test("Baker can compile any valid recipe") {
    val prop = forAll(recipeAddedGen) { message =>
      val bytes = serializer.toBinary(message)
      val deserialized = serializer.fromBinary(bytes, serializer.manifest(message))
      message === deserialized
    }
    check(prop, defaultVerbose.withMinSuccessfulTests(100))
  }
}
