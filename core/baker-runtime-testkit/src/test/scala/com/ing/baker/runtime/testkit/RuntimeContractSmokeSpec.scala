package com.ing.baker.runtime.testkit

import org.scalatest.wordspec.AnyWordSpec
import org.scalatest.matchers.should.Matchers

class RuntimeContractSmokeSpec extends AnyWordSpec with Matchers {

  "Runtime testkit" should {
    "provide a baseline contract adapter type" in {
      val adapter = new RuntimeTestAdapter[String] {
        override val runtimeName: String = "test"
        override def withRuntime(test: String => Any): Any = test("runtime")
      }

      var seen: String = ""
      adapter.withRuntime { runtime =>
        seen = runtime
      }

      adapter.runtimeName shouldBe "test"
      seen shouldBe "runtime"
    }
  }
}

