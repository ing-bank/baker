package com.ing.bakery.interaction.spring

import com.ing.baker.runtime.scaladsl.InteractionInstance
import org.scalatest.flatspec.AnyFlatSpec

class MainTest extends AnyFlatSpec {
  "The main class" should "start all interactions in the given configuration" in {
    val interactions: Seq[InteractionInstance] = Main
      .getImplementations("com.ing.bakery.interaction.spring.TestConfiguration,com.ing.bakery.interaction.spring.TestConfiguration2")
    assert(interactions.size == 4)
  }
}