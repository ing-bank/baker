package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.model.BakerConfig
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class InMemoryMemoryCleanupSpec extends AnyFlatSpec with Matchers {

  behavior of "InMemoryRecipeInstanceManager"

  it should "build Java baker synchronously" in {
    val baker = InMemoryBaker.java(BakerConfig.default(), java.util.List.of())
    baker should not be null
    noException should be thrownBy baker.gracefulShutdown()
  }

  it should "build Java baker asynchronously" in {
    val baker = InMemoryBaker.javaAsync(BakerConfig.default(), java.util.List.of()).join()
    baker should not be null
    noException should be thrownBy baker.gracefulShutdown()
  }
}
