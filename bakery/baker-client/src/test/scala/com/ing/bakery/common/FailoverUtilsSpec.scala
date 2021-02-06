package com.ing.bakery.common

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.scaladsl.EndpointConfig
import org.http4s.Method.GET
import org.http4s._
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.server.blaze.BlazeServerBuilder
import org.scalatest.funspec.FixtureAsyncFunSpec
import org.scalatest.{Assertion, FutureOutcome}

import java.net.InetSocketAddress
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}


class FailoverUtilsSpec extends FixtureAsyncFunSpec   {

  import FailoverUtils._
  implicit val ec: ExecutionContextExecutor = scala.concurrent.ExecutionContext.global
  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(ec)

  implicit val timer: Timer[IO] =
    IO.timer(ec)
  import com.ing.baker.runtime.serialization.JsonDecoders._

  case class Context(client: Client[IO],
                     server200: Uri,
                     server500: Uri,
                     server400: Uri,
                     callbackCollector: IO[Ref[IO, List[String]]])

  def contextBuilder: Resource[IO, Context] = {
    val callbackCollector = Ref.of[IO, List[String]](List.empty)

    for {
      server200 <-
        BlazeServerBuilder[IO](ExecutionContext.global)
          .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
          .withHttpApp(
            Router("/" -> HttpRoutes.of[IO] {
              case _ =>
                callbackCollector.flatMap(_.getAndUpdate(_ :+ "200"))
                Ok("Ok")
            }).orNotFound
          )
          .resource

      server500 <- BlazeServerBuilder[IO](ExecutionContext.global)
      .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
      .withHttpApp(
        Router("/" -> HttpRoutes.of[IO] {
          case _ =>
            callbackCollector.flatMap(_.getAndUpdate(_ :+ "500"))
            InternalServerError()
        }).orNotFound
        )
      .resource

      server400 <- BlazeServerBuilder[IO](ExecutionContext.global)
        .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
        .withHttpApp(
          Router("/" -> HttpRoutes.of[IO] {
            case _ =>
              callbackCollector.flatMap(_.getAndUpdate(_ :+ "400"))
              NotFound()
          }).orNotFound
        )
        .resource

      client <- BlazeClientBuilder[IO](executionContext).resource
    } yield Context(client,
      Uri.unsafeFromString(s"http://localhost:${server200.address.getPort}"),
      Uri.unsafeFromString(s"http://localhost:${server400.address.getPort}"),
      Uri.unsafeFromString(s"http://localhost:${server500.address.getPort}"),
      callbackCollector
    )
  }

  def test(specText: String)(runTest: Context => IO[Assertion]): Unit =
    it(specText)(_ => contextBuilder.use(runTest).unsafeToFuture())

  override type FixtureParam = Unit
  override def withFixture(test: OneArgAsyncTest): FutureOutcome = test.apply(())

//  describe("Failover Service") {
//    test("retries non-fallback request") { context =>
//      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server500, context.server200)))
//      callWithFailOver(fos, context.client,
//        (uri, _) => GET(uri / "app" / "recipes"), Seq.empty,
//        e => IO.raiseError(
//          new RuntimeException(e.toString())
//        ), None)(executionContext, bakerResultDecoder)
//        .unsafeRunSync()
//      for {
//        collector <- context.callbackCollector
//        list <- collector.get
//      } yield assert(list == List("100", "200"))
//    }
//  }

//
//
//  describe("FailoverUtils") {
//
//    val uriA = Uri(path = "baker-a-host")
//    val uriB = Uri(path = "baker-b-host")
//
//    it("Balances 2 hosts") {
//      val fos = new FailoverState(EndpointConfig(IndexedSeq(uriA, uriB)))
//      var index: Int = 0
//      var failoverCalled = false
//      val func: (Uri, String) => IO[Request[IO]] = (uri, prefix) => {
//        println(s"$uri, $prefix")
//        index = index + 1
//        if (index >= 2) {
//          assert(uri == uriB)
//          failoverCalled = true
//          GET(uri / "app" / "recipes")
//        } else {
//          assert(uri == uriA)
//          IO.raiseError(new RuntimeException)
//        }
//      }
//
//      testMethod(fos, func)
//      assert(failoverCalled)
//    }
//
//    it("One host with fallback") {
//      val fos = new FailoverState(EndpointConfig(IndexedSeq(uriA)))
//      var index: Int = 0
//      var fallbackCalled = false
//      val func: (Uri, String) => IO[Request[IO]] = (uri, prefix) => {
//        println(s"$uri $prefix")
//        index = index + 1
//        if (index >= 2) {
//          fallbackCalled = true
//          assert(uri == uriB)
//          GET(uri / "app" / "recipes")
//        } else {
//          assert(uri == uriA)
//            IO.raiseError(new ParsingFailure("error", new RuntimeException("error")))
//        }
//      }
//
//      testMethod(fos, func, Some(EndpointConfig(IndexedSeq(uriB))))
//      assert(fallbackCalled)
//    }
//
//    it("Supports 1 host") {
//      val fos = new FailoverState(EndpointConfig(IndexedSeq(uriA)))
//      var index: Int = 0
//
//      val func: (Uri, String) => IO[Request[IO]] = (uri, _) => {
//
//        index = index + 1
//
//        assert(uri == uriA)
//        if (index >= 2) {
//          GET(uri / "app" / "recipes")
//        } else {
//          IO.raiseError(new RuntimeException)
//        }
//      }
//
//      testMethod(fos, func)
//    }
//
//    it("implements initial configuration for retry") {
//      val config = FailoverUtils.loadConfig
//
//      assert(config.initialDelay == 5.milliseconds)
//      assert(config.retryTimes == 2)
//    }
//  }
//
//  private def testMethod(fos: FailoverState, func: (Uri, String) => IO[Request[IO]], fallbackEndpoint: Option[EndpointConfig] = None): BakerResult = {
//    val client = mock[Client[IO]]
//
//    when(client.expectOr[BakerResult](any[IO[Request[IO]]])(any[Response[IO] => IO[Throwable]])(any[EntityDecoder[IO, BakerResult]]))
//      .thenReturn(IO(mock[BakerResult]))
//
//    val x = callWithFailOver(fos, client, func, Seq.empty,
//      _ => IO.raiseError(new RuntimeException), fallbackEndpoint)(ec, bakerResultDecoder).unsafeRunSync()
//    println(org.mockito.Mockito.mockingDetails(client).printInvocations())
//    x
//  }

}