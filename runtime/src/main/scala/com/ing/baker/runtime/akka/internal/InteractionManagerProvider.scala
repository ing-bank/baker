package com.ing.baker.runtime.akka.internal

import com.typesafe.config.Config

trait InteractionManagerProvider {

  def get(config: Config): InteractionManager

}
