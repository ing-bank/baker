package com.ing.baker.runtime.core

import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.config.{Config, ConfigValueFactory}

class IllegalArgumentTestClass {}

class BakerProviderSpec extends BakerRuntimeTestBase {
  override def actorSystemName = "BakerProviderSpec"

  "The Baker provider" should {

    "give the correct Baker" when {
      "no baker provider configured in application.conf" in {
        val config: Config = defaultActorSystem.settings.config
        val baker = BakerProvider.get(config)
        baker shouldBe a[Baker]
      }

      "if AkkaBakerProvider is configured" in {
        var config: Config = defaultActorSystem.settings.config
        config = config.withValue(
          "baker.engine-provider",
          ConfigValueFactory.fromAnyRef("com.ing.baker.runtime.core.BakerAkkaProvider"))

        val baker = BakerProvider.get(config)
        baker shouldBe a[Baker]
      }
    }
    "throws an error" when {
      "a class without default constructor is provided" in {
        var config: Config = defaultActorSystem.settings.config
        config = config.withValue(
          "baker.engine-provider",
          ConfigValueFactory.fromAnyRef("com.ing.baker.runtime.core.IllegalArgumentTestClass"))
        intercept[IllegalArgumentException] {
          BakerProvider.get(config)
        }
      }

      "a invalid class is provided" in {
        var config: Config = defaultActorSystem.settings.config
        config = config.withValue(
          "baker.engine-provider",
          ConfigValueFactory.fromAnyRef("com.ing.baker.runtime.scaladsl.Baker"))

        intercept[IllegalArgumentException] {
          BakerProvider.get(config)
        }
      }
    }
  }
}
