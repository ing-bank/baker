package com.ing.baker.runtime.akka

import com.ing.baker.BakerAkkaRuntimeTestBase
import com.ing.baker.runtime.testkit.AwaitCompletedRaceConditionSpecLike

class AwaitCompletedRaceConditionSpec extends BakerAkkaRuntimeTestBase with AwaitCompletedRaceConditionSpecLike {

  override def actorSystemName: String = "AwaitCompletedRaceConditionSpec"
}
