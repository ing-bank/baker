package com.ing.baker.runtime.akka

import com.ing.baker.runtime.akka.internal.{InteractionManager, InteractionManagerLocal, InteractionManagerProvider}
import com.typesafe.config.Config

object InteractionManagerProviderTester {
  var called: Boolean = false
}

class InteractionManagerProviderTester extends InteractionManagerProvider {

  override def get(config: Config): InteractionManager = {
    InteractionManagerProviderTester.called = true
    new InteractionManagerLocal()
  }
}
