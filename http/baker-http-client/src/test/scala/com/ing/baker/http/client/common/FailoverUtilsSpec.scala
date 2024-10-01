package com.ing.baker.http.client.common

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.http.client.scaladsl.EndpointConfig
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.scaladsl.BakerResult
import com.ing.baker.runtime.serialization.JsonEncoders._
import org.http4s.Method.GET
import org.http4s._
import org.http4s.circe.jsonEncoderOf
import org.http4s.client.Client
import org.http4s.blaze.client.BlazeClientBuilder
import org.http4s.client.dsl.io._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.blaze.server.BlazeServerBuilder
import org.scalatest.funspec.FixtureAsyncFunSpec
import org.scalatest.{Assertion, FutureOutcome}

import java.net.InetSocketAddress
import scala.annotation.nowarn
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

@nowarn
class FailoverUtilsSpec extends FixtureAsyncFunSpec   {

  import com.ing.baker.http.client.common.FailoverUtils._
  implicit val ec: ExecutionContextExecutor = scala.concurrent.ExecutionContext.global
  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(ec)

  implicit val timer: Timer[IO] =
    IO.timer(ec)
  import com.ing.baker.runtime.serialization.JsonDecoders._
  implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]
  val callbackCollector: mutable.ListBuffer[String] = ListBuffer.empty

  case class Context(client: Client[IO],
                     server200: Uri,
                     server400: Uri,
                     server404: Uri,
                     server500: Uri)

  def contextBuilder: Resource[IO, Context] = {

    for {
      server200 <-
        BlazeServerBuilder[IO](ExecutionContext.global)
          .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
          .withHttpApp(
            Router("/" -> HttpRoutes.of[IO] {
              case _ =>
                for {
                  response <- Ok(BakerResult(List.empty[Int]))
                } yield {
                  callbackCollector.append("200")
                  response
                }
            }).orNotFound
          )
          .resource

      server500 <- BlazeServerBuilder[IO](ExecutionContext.global)
      .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
      .withHttpApp(
        Router("/" -> HttpRoutes.of[IO] {
          case _ =>
            callbackCollector.append("500")
            InternalServerError()
        }).orNotFound
        )
      .resource

      server404 <- BlazeServerBuilder[IO](ExecutionContext.global)
        .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
        .withHttpApp(
          Router("/" -> HttpRoutes.of[IO] {
            case _ =>
              callbackCollector.append("404")
              NotFound()
          }).orNotFound
        )
        .resource

      server400 <- BlazeServerBuilder[IO](ExecutionContext.global)
        .bindSocketAddress( InetSocketAddress.createUnresolved("localhost", 0))
        .withHttpApp(
          Router("/" -> HttpRoutes.of[IO] {
            case _ =>
              callbackCollector.append("400")
              NotFound()
          }).orNotFound
        )
        .resource

      client <- BlazeClientBuilder[IO](executionContext).resource
    } yield Context(client,
      Uri.unsafeFromString(s"http://localhost:${server200.address.getPort}"),
      Uri.unsafeFromString(s"http://localhost:${server400.address.getPort}"),
      Uri.unsafeFromString(s"http://localhost:${server404.address.getPort}"),
      Uri.unsafeFromString(s"http://localhost:${server500.address.getPort}")
    )
  }

  def test(specText: String)(runTest: Context => IO[Assertion]): Unit =
    it(specText)(_ => contextBuilder.use(runTest).unsafeToFuture())

  override type FixtureParam = Unit
  override def withFixture(test: OneArgAsyncTest): FutureOutcome = test.apply(())

  describe("Failover utils") {
    test("processes non-fallback request after 500") { context =>
      callbackCollector.clear()
      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server500, context.server200)))
      for {
        result <- callWithFailOver(fos, context.client,
          (uri, _) => IO(GET(uri / "app" / "recipes")), Seq.empty,
          FailoverUtils.handleHttpErrors, None)(executionContext, bakerResultDecoder)
      } yield {
        assert(result == BakerResult(List.empty[Int]))
        assert(callbackCollector.toList == List("500", "200"))
      }
    }

    test("falls back after 400") { context =>
      callbackCollector.clear()
      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server400, context.server500)))
      for {
        _ <- callWithFailOver(fos, context.client,
          (uri, _) => IO(GET(uri / "app" / "recipes")), Seq.empty,
          FailoverUtils.handleFallbackAwareErrors, Some(EndpointConfig(IndexedSeq(context.server200))))(executionContext, bakerResultDecoder)
      } yield {
        assert(callbackCollector.toList == List("400", "200"))
      }
    }

    test("processes fallback request after 500 and then 400") { context =>
      callbackCollector.clear()
      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server500, context.server400)))
      for {
        result <- callWithFailOver(fos, context.client,
          (uri, _) => IO(GET(uri / "app" / "recipes")), Seq.empty,
          FailoverUtils.handleFallbackAwareErrors, Some(EndpointConfig(IndexedSeq(context.server200))))(executionContext, bakerResultDecoder)
      } yield {
        assert(result == BakerResult(List.empty[Int]))
        assert(callbackCollector.toList == List("500", "400", "200"))
      }
    }

    test ("Return correct NoSuchProcessException") { context =>
      callbackCollector.clear()
      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server404)))

      for {
        either <- callWithFailOver(fos, context.client,
          (uri, _) => IO(GET(uri / "app" / "recipes")), Seq.empty,
          FailoverUtils.handleFallbackAwareErrors, None)(executionContext, bakerResultDecoder).attempt
      } yield {
        assert(either.left.get.isInstanceOf[NoSuchProcessException])
      }
    }

    test ("Return correct NoSuchProcessException after retry") { context =>
      callbackCollector.clear()
      val fos = new FailoverState(EndpointConfig(IndexedSeq(context.server404)))

      for {
        either <- callWithFailOver(fos, context.client,
          (uri, _) => IO(GET(uri / "app" / "recipes")), Seq.empty,
          FailoverUtils.handleFallbackAwareErrors,
            Some(EndpointConfig(IndexedSeq(context.server404, context.server404))))(executionContext, bakerResultDecoder).attempt
      } yield {
        assert(either.left.get.isInstanceOf[NoSuchProcessException])
      }
    }
  }
}
