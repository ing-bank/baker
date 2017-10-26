package com.ing.baker.recipe.common

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

  }
}
