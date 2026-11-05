package com.ing.baker.runtime.akka

import com.ing.baker.BakerPekkoRuntimeTestBase
import com.ing.baker.runtime.testkit.ExampleSpecLike

class ExamplesSpec extends BakerPekkoRuntimeTestBase with ExampleSpecLike {
  override def actorSystemName = "ExamplesSpec"
}
