package com.ing.bakery.smoke

import com.ing.bakery.testing.BakeryFunSpec
import org.http4s.Uri
import org.scalatest.ConfigMap

abstract class BakerySmokeTests  extends BakeryFunSpec {

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = BakeryEnvironment.Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = BakeryEnvironment.Arguments

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
   *
   * @param config map populated with the -Dkey=value arguments.
   * @return the data structure used by the `contextBuilder` function.
   */
  def argumentsBuilder(config: ConfigMap): TestArguments = {
    val clientAppHostname = Uri.unsafeFromString(
      config.getOptional[String]("client-app").getOrElse("http://localhost:8082"))
    BakeryEnvironment.Arguments(
      clientAppHostname = clientAppHostname
    )
  }


}
