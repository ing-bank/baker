package com.ing.baker.runtime.akka

import com.ing.baker.BakerAkkaRuntimeTestBase
import com.ing.baker.runtime.testkit.ExampleSpecLike

class ExamplesSpec extends BakerAkkaRuntimeTestBase with ExampleSpecLike {
  override def actorSystemName = "ExamplesSpec"
}
