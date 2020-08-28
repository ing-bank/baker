package com.ing.baker.recipe.common

import com.ing.baker.recipe.common.HashingSpec._
import com.ing.baker.types
import com.ing.baker.types._
import org.scalacheck.Prop.forAll
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalacheck.{Arbitrary, Gen, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers

class HashingSpec extends AnyFunSuite with Checkers {

  val config: Test.Parameters =
    defaultVerbose.withMinSuccessfulTests(minSuccessfulTests = 1000)

  def hashingLaw[A: Arbitrary](): Unit = {
    check(forAll { (x: A, y: A) =>
      if (x == y) x.hashCode() == y.hashCode()
      else x.hashCode() != y.hashCode()
    }, config)
  }

  test("Type hashing")(hashingLaw[Type]())

  test("Ingredient hashing")(hashingLaw[Ingredient]())

  test("Event hashing")(hashingLaw[Event]())
}

object HashingSpec {

  implicit def arbitraryType: Arbitrary[Type] =
    Arbitrary(typeGen)

  implicit def arbitraryIngredient: Arbitrary[Ingredient] =
    Arbitrary(ingredientGen)

  implicit def arbitraryEvent: Arbitrary[Event] =
    Arbitrary(eventGen)

  def ingredientGen: Gen[Ingredient] =
    for {
      name0 <- fieldNameGen
      type0 <- typeGen
    } yield new Ingredient(name0, type0)

  def eventGen: Gen[Event] =
    for {
      name0 <- fieldNameGen
      ingredients0 <- Gen.listOf(ingredientGen)
    } yield new Event {
      override val name: String = name0
      override val providedIngredients: Seq[Ingredient] = ingredients0
    }

  def typeGen: Gen[Type] =
    Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

  def fieldNameGen: Gen[String] =
    Gen.alphaStr

  def primitiveTypeGen: Gen[Type] =
    Gen.oneOf(types.primitiveTypes.toSeq)

  def fieldTypeGen: Gen[Type] =
    primitiveTypeGen

  def recordTypeEntries: Gen[RecordField] = for {
    fieldName <- fieldNameGen
    fieldType <- fieldTypeGen
  } yield RecordField(fieldName, fieldType)

  def recordTypeGen: Gen[RecordType] =
    Gen.listOf(recordTypeEntries).map(RecordType(_))

  def listTypeGen: Gen[ListType] =
    primitiveTypeGen.map(ListType)

  def mapTypeGen: Gen[MapType] =
    primitiveTypeGen.map(MapType)

  def optionTypeGen: Gen[OptionType] =
    primitiveTypeGen.map(OptionType)
}