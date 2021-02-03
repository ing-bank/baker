package com.ing.bakery.common

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.scaladsl.BakerResult
import io.circe.ParsingFailure
import org.http4s.Method.GET
import org.http4s._
import org.http4s.client.Client
import org.http4s.client.dsl.io._
import org.http4s.dsl.impl.Root
import org.mockito.scalatest.MockitoSugar
import org.scalatest.funspec.AnyFunSpec

import java.util.concurrent.{ExecutorService, Executors}
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor, ExecutionContextExecutorService}
import scala.concurrent.duration._


class FailoverUtilsSpec extends AnyFunSpec with MockitoSugar {

  import FailoverUtils._

  implicit val ec: ExecutionContextExecutor = scala.concurrent.ExecutionContext.global

  import com.ing.baker.runtime.serialization.JsonDecoders._

  describe("FailoverUtils") {

    val uriA = Uri(path = "baker-a-host")
    val uriB = Uri(path = "baker-b-host")

    it("Balances 2 hosts") {
      val fos = new FailoverState(IndexedSeq(uriA, uriB))
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

    it("Balances two legacy hosts") {
      val fos = new FailoverState(IndexedSeq(uriA), IndexedSeq(uriB))
      var index: Int = 0

      val func: Uri => IO[Request[IO]] = (uri) => {

        index = index + 1
        if (index >= 2) {
          assert(uri == uriB)
          GET(uri / "app" / "recipes")
        } else {
          assert(uri == uriA)
            IO.raiseError(new ParsingFailure("error", new RuntimeException("error")))
        }
      }

      testMethod(fos, func)
    }


    it("Supports 1 host") {
      val fos = new FailoverState(IndexedSeq(uriA))
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

    it("implements initial configuration for retry") {
      val config = FailoverUtils.loadConfig

      assert(config.initialDelay == 5.milliseconds)
      assert(config.retryTimes == 2)
    }

//    it("404 example") {
//      import cats.effect._
//      import org.http4s._
//      import org.http4s.dsl.io._
//      import org.http4s.implicits._
//      import org.http4s.server.blaze._
//
//      import scala.concurrent.ExecutionContext.global
//      implicit val cs: ContextShift[IO] = IO.contextShift(global)
//      implicit val timer: Timer[IO] = IO.timer(global)
//
//      val app = HttpRoutes.of[IO] {
//        case org.http4s.dsl.io.GET -> org.http4s.dsl.io.Root / "hello" / name =>
//          Ok(s"Hello, $name.")
//      }.orNotFound
//
//
//      val server = BlazeServerBuilder[IO](global).bindHttp(8085, "localhost").withHttpApp(app).resource
//
//      val fiber = server.use(_ => IO.never).start.unsafeRunSync()
//
//      import org.http4s.client.blaze._
//      import org.http4s.client._
//
//
//      val service: ExecutorService = Executors.newFixedThreadPool(5)
//      val httpClient: Client[IO] = JavaNetClientBuilder[IO](Blocker.liftExecutorService(service)).create
//
//      val helloJames = httpClient.expect[String]("http://localhost:8085/James")
//      println(helloJames.unsafeRunSync())
//
//    }
  }

  private def testMethod(fos: FailoverState, func: Uri => IO[Request[IO]]): BakerResult = {
    val client = mock[Client[IO]]

    when(client.expectOr(any[IO[Request[IO]]])(any[Response[IO] => IO[Throwable]])(any[EntityDecoder[IO, BakerResult]]))
      .thenReturn(IO(mock[BakerResult]))

    callWithFailOver(fos, client, func, Seq.empty, _ => IO.raiseError(new RuntimeException))(ec, bakerResultDecoder).unsafeRunSync()
  }
}