package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.runtime.testkit.BakerSetupSpecLike
import io.prometheus.client.CollectorRegistry

import scala.annotation.nowarn
import scala.language.postfixOps

@nowarn
class BakerSetupSpec extends BakerAkkaRuntimeTestBase with BakerSetupSpecLike {

  override def actorSystemName = "BakerSetupSpec"

  before {
    resetMocks()
  }

  override def beforeAll() = {
    CollectorRegistry.defaultRegistry.clear()
  }
}
