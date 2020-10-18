package com.ing.bakery.common

import cats.effect.IO
import com.ing.baker.runtime.scaladsl.{BakerResult, EventInstance}
import com.ing.baker.runtime.serialization.JsonEncoders._
import org.http4s.Method.GET
import org.http4s.circe.jsonEncoderOf
import org.http4s.client.Client
import org.http4s.client.dsl.io._
import org.http4s._
import org.mockito.scalatest.MockitoSugar
import org.scalatest.funspec.AnyFunSpec

import scala.concurrent.ExecutionContextExecutor
import scala.reflect.ClassTag


class FailoverUtilsSpec extends AnyFunSpec with MockitoSugar {

  import FailoverUtils._

  implicit val ec: ExecutionContextExecutor = scala.concurrent.ExecutionContext.global

  import com.ing.baker.runtime.serialization.JsonDecoders._

  describe("FailoverUtils") {

    val uriA = Uri(path = "baker-a-host")
    val uriB = Uri(path = "baker-b-host")

    it("Balances 2 hosts") {
      val fos = new FailoverState(List(uriA, uriB))
      var index: Int = 0

      val func: Uri => IO[Request[IO]] = (uri) => {

        index = index + 1
        if (index >= 2) {
          assert(uri == uriB)
          GET(uri / "app" / "recipes")
        } else {
          assert(uri == uriA)
          IO.raiseError(new RuntimeException)
        }
      }

      testMethod(fos, func)
    }

    it("Supports 1 host") {
      val fos = new FailoverState(List(uriA))
      var index: Int = 0

      val func: Uri => IO[Request[IO]] = (uri) => {

        index = index + 1

        assert(uri == uriA)
        if (index >= 2) {
          GET(uri / "app" / "recipes")
        } else {
          IO.raiseError(new RuntimeException)
        }
      }

      testMethod(fos, func)
    }
  }

  private def testMethod(fos: FailoverState, func: Uri => IO[Request[IO]]): BakerResult = {
    val client = mock[Client[IO]]

    when(client.expectOr(any[IO[Request[IO]]])(any[Response[IO] => IO[Throwable]])(any[EntityDecoder[IO, BakerResult]]))
      .thenReturn(IO(mock[BakerResult]))

    calWithFailOver(fos, client, func, Seq.empty, _ => IO.raiseError(new RuntimeException))( ec, bakerResultDecoder).unsafeRunSync()
  }
}