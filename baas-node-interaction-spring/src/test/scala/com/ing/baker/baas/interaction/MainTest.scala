package com.ing.baker.baas.interaction

import com.ing.baker.runtime.scaladsl.InteractionInstance
import org.scalatest.flatspec.AnyFlatSpec

class MainTest extends AnyFlatSpec {
  "The main class" should "start all interactions in the given configuration" in {
    val interactions: Seq[InteractionInstance] = com.ing.baker.baas.interaction.spring.Main
      .getImplementations("com.ing.baker.baas.interaction.TestConfiguration")
    assert(interactions.size == 2)
  }
}