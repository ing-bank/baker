package com.ing.baker.runtime.catseffect

import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

import java.util.concurrent.{CompletionException, TimeUnit}

class SyncSupportCompletableFutureSpec extends AnyFunSpec with Matchers {

  private val timeout = 2L

  describe("SyncSupport CompletableFuture implementation") {
    it("supports pure/map/flatMap composition") {
      val sync = SyncSupport.fromCompletableFuture

      val result = sync.flatMap(sync.map(sync.pure(1))(_ + 1))(value => sync.pure(value * 2))

      result.get(timeout, TimeUnit.SECONDS) shouldBe 4
    }

    it("captures delay exceptions as failed futures") {
      val sync = SyncSupport.fromCompletableFuture

      val failure = sync.delay[Int](throw new IllegalStateException("boom"))

      val thrown = intercept[CompletionException] {
        failure.join()
      }
      thrown.getCause shouldBe a[IllegalStateException]
      thrown.getCause.getMessage shouldBe "boom"
    }

    it("creates a failed future for raiseError") {
      val sync = SyncSupport.fromCompletableFuture

      val failure = sync.raiseError[Int](new RuntimeException("failed"))

      val thrown = intercept[CompletionException] {
        failure.join()
      }
      thrown.getCause.getMessage shouldBe "failed"
    }
  }

  describe("SyncSupport CompletionStage implementation") {
    it("supports composition and returns completion results") {
      val sync = SyncSupport.fromCompletionStage

      val stage = sync.flatMap(sync.pure("baker"))(value => sync.pure(value.reverse))

      stage.toCompletableFuture.get(timeout, TimeUnit.SECONDS) shouldBe "rekab"
    }

    it("runs blocking computations") {
      val sync = SyncSupport.fromCompletionStage

      val stage = sync.blocking("ok")

      stage.toCompletableFuture.get(timeout, TimeUnit.SECONDS) shouldBe "ok"
    }
  }
}

