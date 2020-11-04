package com.ing.baker.runtime.model

import scala.concurrent.duration._

case class BakerConfig(
                        allowAddingRecipeWithoutRequiringInstances: Boolean = false,
                        bakeTimeout: FiniteDuration = 10.seconds,
                        processEventTimeout: FiniteDuration = 10.seconds,
                        inquireTimeout: FiniteDuration = 10.seconds,
                        shutdownTimeout: FiniteDuration = 10.seconds,
                        addRecipeTimeout: FiniteDuration = 10.seconds
                      )
