package com.ing.baker.runtime.inmemory

import com.ing.baker.runtime.model.BakerConfig
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import java.util.concurrent.CompletableFuture
import scala.collection.immutable.{List => ScalaList}

class InMemoryBakerSpec extends AnyFlatSpec with Matchers {

  behavior of "InMemoryBaker"

  it should "build and shutdown with CompletableFuture backend" in {
    val baker = InMemoryBaker
      .build(BakerConfig.default(), ScalaList.empty[Any])
      .join()
      .asInstanceOf[com.ing.baker.runtime.model.BakerF[CompletableFuture]]

    noException should be thrownBy baker.gracefulShutdown().join()
  }

  it should "provide Java facade through async factory" in {
    val javaBaker = InMemoryBaker
      .javaAsync(BakerConfig.default(), java.util.List.of())
      .join()

    javaBaker should not be null
    noException should be thrownBy javaBaker.gracefulShutdown()
  }
}
