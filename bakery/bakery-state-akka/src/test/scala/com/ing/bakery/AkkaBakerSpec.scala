package com.ing.bakery

import cats.effect.{IO, Resource}
import com.ing.bakery.components.NoopComponents
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.scalatest.ConfigMap
import org.scalatest.matchers.should

class AkkaBakerSpec extends BakeryFunSpec with should.Matchers {

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = AkkaBakery

  /** Represents external arguments to the test context builder. */
  type TestArguments = Unit

  override def contextBuilder(testArguments: Unit): Resource[IO, AkkaBakery] =
    Bakery.akkaBakery(
      optionalConfig = Some(ConfigFactory.load("application-akkabakeryspec.conf")),
      interactionManager = Some(NoopComponents.TestInteractionManager),
    )

  override def argumentsBuilder(config: ConfigMap): Unit = ()

  describe("AkkaBakery") {
    test("start correctly and respond to call") { akkaBakery =>
      IO.fromFuture(IO(akkaBakery.baker.getAllInteractions)).map(ai => ai shouldEqual List())
    }
  }

}
