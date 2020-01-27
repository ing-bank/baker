package com.ing.baker.runtime.akka

import akka.actor.ActorSystem
import com.typesafe.config.ConfigFactory
import org.scalatest.{Matchers, WordSpecLike}
import org.scalatestplus.mockito.MockitoSugar

class InteractionManagerSpec
  extends WordSpecLike
  with Matchers
  with MockitoSugar {

  "The InteractionManager" should {

    "default to the InteractionManagerLocal" in {

      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |""".stripMargin).withFallback(ConfigFactory.load())

      val actorSystem = ActorSystem("InteractionManagerSpec")

      val baker = AkkaBaker(config, actorSystem)
    }

    "use configured InteractionManagerProvider if configured" in {

      InteractionManagerProviderTester.called = false

      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          | baker.interaction-manager.provider = "com.ing.baker.runtime.akka.InteractionManagerProviderTester"
          |""".stripMargin).withFallback(ConfigFactory.load())

      val actorSystem = ActorSystem("InteractionManagerSpec")

      AkkaBaker(config, actorSystem)

      InteractionManagerProviderTester.called shouldBe true
    }

    "fail starting if an invalid InteractionManagerProvider is configured" in {

      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          | baker.interaction-manager.provider = "com.ing.baker.runtime.akka.Invalid"
          |""".stripMargin).withFallback(ConfigFactory.load())

      val actorSystem = ActorSystem("InteractionManagerSpec")
      val caught = intercept[IllegalArgumentException](AkkaBaker(config, actorSystem))
      caught.getMessage shouldBe "Could not load InteractionManager from provider from: com.ing.baker.runtime.akka.Invalid"
    }
  }
}
