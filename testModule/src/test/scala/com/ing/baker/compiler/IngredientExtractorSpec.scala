package com.ing.baker.compiler

import com.ing.baker.compiledRecipe.ingredientExtractors.{CompositeIngredientExtractor, IngredientExtractor}
import com.typesafe.config.ConfigFactory
import org.scalatest.{Matchers, WordSpecLike}

class TestIngredientExtractor extends IngredientExtractor {

  override def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]] = ???

  override def extractIngredientData(obj: Any): Map[String, Any] = ???
}

trait TestAnchorPoint

class IngredientExtractorSpec extends WordSpecLike with Matchers {

  "The CompositeIngredient extractor" should {

    "Pick the most specific extractor for a given type" in {

      val testConfig =
        """
          | baker {
          |
          |   ingredient-extractors {
          |     "default" = com.ing.baker.compiledRecipe.ingredientExtractors.PojoIngredientExtractor
          |     "test" = "com.ing.baker.compiler.TestIngredientExtractor"
          |   }
          |
          |   ingredient-extractor-bindings {
          |     "java.lang.Object" = "default"
          |     "com.ing.baker.compiler.TestAnchorPoint" = "test"
          |   }
          | }
          |
        """.stripMargin

      val extractor = new CompositeIngredientExtractor(ConfigFactory.parseString(testConfig))

      println(extractor.extractorForClass(classOf[TestAnchorPoint]))
    }
  }
}
