package com.ing.bakery.common

import org.http4s.Uri
import org.scalatest.funspec.AnyFunSpec

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}


class FailoverStateSpec extends AnyFunSpec {

  private val uriA = Uri(path = "baker-a-host")
  private val uriB = Uri(path = "baker-b-host")
  private val uriC = Uri(path = "baker-c-host")

  describe("Balancer") {

    it("should support single element list") {

      val fos = new FailoverState(IndexedSeq(uriA))

      assert(fos.uri == uriA)

      fos.failed()

      assert(fos.uri == uriA)

      (1 to 10).foreach(_ => fos.failed())
      assert(fos.uri == uriA)
    }


    it("should fail without elements") {

      val fos = new FailoverState(IndexedSeq.empty)

      assertThrows[IndexOutOfBoundsException](fos.uri)

      fos.failed()

      assertThrows[IndexOutOfBoundsException](fos.uri)
    }

    it("should support multiply elements") {
      val fos = new FailoverState(IndexedSeq(uriA, uriB))

      assert(fos.uri == uriA)

      fos.failed()

      assert(fos.uri == uriB)

      fos.failed()

      assert(fos.uri == uriA)

      implicit val ec: scala.concurrent.ExecutionContext = scala.concurrent.ExecutionContext.global

      val result = Future.sequence(
        (1 to 1000).map(_ => Future {
          fos.failed()
          val currentHost = fos.uri // Because of concurrency checking host at any random time
          assert(currentHost == uriA || currentHost == uriB)
        }))

      Await.result(result, 5.seconds)
    }
  }
}