package com.ing.baker.http.server.scaladsl

import com.typesafe.config.ConfigFactory
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should

class Http4sBakerServerConfigurationSpec extends AnyFlatSpec with should.Matchers {

  "Http4sBakerServiceConfiguration" should "load by default" in {
    Http4sBakerServerConfiguration.fromConfig(ConfigFactory.load()) shouldBe Http4sBakerServerConfiguration(
      "0.0.0.0",
      8080,
      "/api/bakery",
      loggingEnabled = false
    )
  }
}
