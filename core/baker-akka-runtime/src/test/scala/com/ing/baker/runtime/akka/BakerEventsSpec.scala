package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.runtime.testkit.BakerEventsSpecLike

import scala.language.postfixOps

class BakerEventsSpec extends BakerAkkaRuntimeTestBase with BakerEventsSpecLike {

  override def actorSystemName = "BakerEventsSpec"

  before {
    resetMocks()
    setupMockResponse()
  }
}
