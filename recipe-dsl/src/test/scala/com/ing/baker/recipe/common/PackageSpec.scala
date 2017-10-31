package com.ing.baker.recipe.common

import com.ing.baker.recipe.common.ingredients.{ComplexPOJOExample, EnumExample, SimplePOJOExample}
import org.scalatest.{Matchers, WordSpecLike}

class PackageSpec extends WordSpecLike with Matchers {

  "The type" should {

    "correctly parse all the supported base types" in {
      supportedBaseTypes.foreach { t =>
        ingredientTypeFromType(t) shouldBe BaseType(t)
      }
    }

    "correctly parse option types" in {
      ingredientTypeFromType(makeType[Option[String]]) shouldBe OptionType(BaseType(classOf[String]))
    }

    "correctly parse list types" in {
      ingredientTypeFromType(makeType[List[String]]) shouldBe ListType(BaseType(classOf[String]))
    }

    "correctly parse enum types" in {
      ingredientTypeFromType(classOf[EnumExample]) shouldBe EnumType(options = Set("A", "B", "C"))
    }

    "correctly parse basic POJO types" in {
      val simplePOJOExampleSeq = Seq(
        new Ingredient("integer", BaseType(classOf[Integer])),
        new Ingredient("string", BaseType(classOf[String])),
        new Ingredient("boolean", BaseType(classOf[Boolean])))

      ingredientTypeFromType(classOf[SimplePOJOExample]) shouldBe POJOType(simplePOJOExampleSeq)
    }

    "correctly parse POJO types in POJO types" in {
      val simplePOJOExampleSeq = Seq(
        new Ingredient("integer", BaseType(classOf[Integer])),
        new Ingredient("string", BaseType(classOf[String])),
        new Ingredient("boolean", BaseType(classOf[Boolean])))

      val complexPOJOExampleSeq = Seq(
        new Ingredient("simplePOJOExample", POJOType(simplePOJOExampleSeq)),
        new Ingredient("string", BaseType(classOf[String])),
        new Ingredient("boolean", BaseType(classOf[Boolean])))

      ingredientTypeFromType(classOf[ComplexPOJOExample]) shouldBe POJOType(complexPOJOExampleSeq)
    }

  }
}
