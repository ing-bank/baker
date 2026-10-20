package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.ScalaDSLRuntime._
import com.ing.baker.runtime.akka.implementations.{InteractionOneFieldName, InteractionOneInterfaceImplementation, InteractionOneWrongApply}
import com.ing.baker.runtime.core.util.CachingInteractionManager
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, RecipeValidationException}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.runtime.testkit.{BakerInquireSpecLike, BakerSetupSpecLike}
import com.typesafe.config.ConfigFactory
import io.prometheus.client.CollectorRegistry
import org.mockito.ArgumentMatchers.anyString
import org.mockito.Mockito.when

import scala.annotation.nowarn
import scala.concurrent.Future
import scala.language.postfixOps

@nowarn
class BakerSetupSpec extends BakerPekkoRuntimeTestBase with BakerSetupSpecLike {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks()
  }

  override def beforeAll() = {
    CollectorRegistry.defaultRegistry.clear()
  }
}
