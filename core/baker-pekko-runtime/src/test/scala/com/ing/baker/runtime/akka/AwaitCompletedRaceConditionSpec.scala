package com.ing.baker.runtime.akka

import com.ing.baker.BakerPekkoRuntimeTestBase
import com.ing.baker.runtime.testkit.AwaitCompletedRaceConditionSpecLike

class AwaitCompletedRaceConditionSpec extends BakerPekkoRuntimeTestBase with AwaitCompletedRaceConditionSpecLike {

  override def actorSystemName: String = "AwaitCompletedRaceConditionSpec"
}
