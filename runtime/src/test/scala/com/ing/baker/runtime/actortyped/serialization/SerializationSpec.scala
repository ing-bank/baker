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
import com.ing.baker.runtime.actortyped.recipe_manager.RecipeManagerSerialization

class SerializationSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Checkers {

  println("================== 00")
  val serializer: BakerProtobufSerializer = SerializationExtension.get(system).serializerByIdentity(102).asInstanceOf[BakerProtobufSerializer]
  println("================== 01")

  val recipeAddedGen: Gen[RecipeAdded] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeAdded(recipe, timestamp)

  test("Baker can compile any valid recipe") {
    println("================== 1")
    /*
    val prop = forAll(recipeAddedGen) { message =>
      val bytes = serializer.toBinary(message)
      val deserialized = serializer.fromBinary(bytes, serializer.manifest(RecipeManagerSerialization.recipeAddedManifest))
      message === deserialized
    }
    check(prop, defaultVerbose.withMinSuccessfulTests(100))
    */
    val message = recipeAddedGen.sample.get
    println("================== 2")
    val bytes = serializer.toBinary(message)
    println("================== 3")
    val deserialized = serializer.fromBinary(bytes, serializer.manifest(RecipeManagerSerialization.recipeAddedManifest))
    println("================== 4")
    message === deserialized
  }
}
