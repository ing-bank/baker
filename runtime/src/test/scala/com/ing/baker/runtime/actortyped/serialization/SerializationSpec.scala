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
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol

class SerializationSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Checkers {

  val serializer: BakerTypedProtobufSerializer = SerializationExtension.get(system).serializerByIdentity(103).asInstanceOf[BakerTypedProtobufSerializer]

  val addRecipe: Gen[RecipeManagerProtocol.AddRecipe] =
    for {
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.AddRecipe(recipe)

  val addRecipeResponse: Gen[RecipeManagerProtocol.AddRecipeResponse] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.AddRecipeResponse(recipeId)

  val getRecipe: Gen[RecipeManagerProtocol.GetRecipe] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.GetRecipe(recipeId)

  val recipeFound: Gen[RecipeManagerProtocol.RecipeFound] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.RecipeFound(recipe, timestamp)

  val noRecipeFound: Gen[RecipeManagerProtocol.NoRecipeFound] =
    for {
      recipeId <- Gen.alphaNumStr
    } yield RecipeManagerProtocol.NoRecipeFound(recipeId)

  val allRecipes: Gen[RecipeManagerProtocol.AllRecipes] =
    for {
      timestamp <- Gen.chooseNum(0l, 20000l)
      recipe <- recipeGen.map(RecipeCompiler.compileRecipe)
    } yield RecipeManagerProtocol.AllRecipes(Seq(RecipeManagerProtocol.RecipeInformation(recipe, timestamp)))

  test("RecipeManagerProtocol.AddRecipe typed serialization") {
    check(forAll(addRecipe)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

  test("RecipeManagerProtocol.AddRecipeResponse typed serialization") {
    check(forAll(addRecipeResponse)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

  test("RecipeManagerProtocol.GetRecipe typed serialization") {
    check(forAll(getRecipe)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

  test("RecipeManagerProtocol.RecipeFound typed serialization") {
    check(forAll(recipeFound)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

  test("RecipeManagerProtocol.NoRecipeFound typed serialization") {
    check(forAll(noRecipeFound)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

  test("RecipeManagerProtocol.GetAllRecipes typed serialization") {
    RecipeManagerProtocol.GetAllRecipes == serializer.fromBinary(serializer.toBinary(RecipeManagerProtocol.GetAllRecipes), serializer.manifest(RecipeManagerProtocol.GetAllRecipes))
  }

  test("RecipeManagerProtocol.AllRecipes typed serialization") {
    check(forAll(allRecipes)(m =>
      m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
      defaultVerbose.withMinSuccessfulTests(10)
    )
  }

}
