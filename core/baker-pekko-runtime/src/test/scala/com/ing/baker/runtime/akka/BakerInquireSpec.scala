package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.runtime.testkit.BakerInquireSpecLike

import scala.language.postfixOps

class BakerInquireSpec extends BakerPekkoRuntimeTestBase with BakerInquireSpecLike {

  override def actorSystemName = "BakerInquireSpec"

  before {
    resetMocks()
    setupMockResponse()
  }
}