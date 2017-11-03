package com.ing.baker.recipe.common

import com.ing.baker.recipe.common.ingredients.{ComplexPOJOExample, EnumExample, SimplePOJOExample}
import org.scalatest.{Matchers, WordSpecLike}

class PackageSpec extends WordSpecLike with Matchers {

  "The type" should {

    "correctly parse all the supported base types" in {
      supportedPrimitiveClasses.foreach { t =>
        ingredientTypeFromType(t) shouldBe PrimitiveType(t)
      }
    }

    "correctly parse option types" in {
      ingredientTypeFromType(makeType[Option[String]]) shouldBe OptionType(PrimitiveType(classOf[String]))
    }

    "correctly parse list types" in {
      ingredientTypeFromType(makeType[List[String]]) shouldBe ListType(PrimitiveType(classOf[String]))
    }

    "correctly parse enum types" in {
      ingredientTypeFromType(classOf[EnumExample]) shouldBe EnumType(options = Set("A", "B", "C"))
    }

    "correctly parse basic POJO types" in {
      val simplePOJOExampleSeq = Seq(
        new Ingredient("integer", PrimitiveType(classOf[Integer])),
        new Ingredient("string", PrimitiveType(classOf[String])),
        new Ingredient("boolean", PrimitiveType(classOf[Boolean])))

      ingredientTypeFromType(classOf[SimplePOJOExample]) shouldBe POJOType(simplePOJOExampleSeq)
    }

    "correctly parse POJO types in POJO types" in {
      val simplePOJOExampleSeq = Seq(
        new Ingredient("integer", PrimitiveType(classOf[Integer])),
        new Ingredient("string", PrimitiveType(classOf[String])),
        new Ingredient("boolean", PrimitiveType(classOf[Boolean])))

      val complexPOJOExampleSeq = Seq(
        new Ingredient("simplePOJOExample", POJOType(simplePOJOExampleSeq)),
        new Ingredient("string", PrimitiveType(classOf[String])),
        new Ingredient("boolean", PrimitiveType(classOf[Boolean])))

      ingredientTypeFromType(classOf[ComplexPOJOExample]) shouldBe POJOType(complexPOJOExampleSeq)
    }

  }
}
