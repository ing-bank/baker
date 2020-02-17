package com.ing.baker.baas.smoke

import scala.sys.process._
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalactic.source
import org.scalatest.compatible.Assertion
import org.scalatest.{FutureOutcome, Tag, fixture}

import scala.concurrent.duration._

abstract class BakeryFunSpec extends fixture.AsyncFunSpecLike {

  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(executionContext)

  implicit val timer: Timer[IO] =
    IO.timer(executionContext)

  def eventually[A](f: IO[A]): IO[A] =
    within(20.seconds, 20)(f)

  def within[A](time: FiniteDuration, split: Int)(f: IO[A]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

  case class TestContext(
    clientApp: ExampleAppClient
  )

  case class TestArguments(
                            clientAppHostname: Uri,
                            stateServiceHostname: Uri,
                            eventListenerHostname: Uri,
                            bakerEventListenerHostname:Uri,
                            skipSetup: Boolean,
                            skipCleanup: Boolean
  )

  override type FixtureParam = TestArguments

  override def withFixture(test: OneArgAsyncTest): FutureOutcome = {
    val clientAppHostname = Uri.unsafeFromString(
      test.configMap.getOptional[String]("client-app").getOrElse("http://localhost:8080"))
    val stateServiceHostname = Uri.unsafeFromString(
      test.configMap.getOptional[String]("state-service").getOrElse("http://localhost:8081"))
    val eventListenerHostname = Uri.unsafeFromString(
      test.configMap.getOptional[String]("event-listener").getOrElse("http://localhost:8082"))
    val bakerEventListenerHostname = Uri.unsafeFromString(
      test.configMap.getOptional[String]("baker-event-listener").getOrElse("http://localhost:8083"))
    val skipSetup = {
      val skip = test.configMap.getOptional[String]("skip-setup").getOrElse("false")
      skip == "true" || skip == "t" || skip == "1" || skip == "yes"
    }
    val  skipCleanup= {
      val  skipCleanup= test.configMap.getOptional[String]("skip-cleanup").getOrElse("false")
       skipCleanup== "true" ||  skipCleanup== "t" ||  skipCleanup== "1" ||  skipCleanup== "yes"
    }
    test.apply(TestArguments(
      clientAppHostname = clientAppHostname,
      stateServiceHostname = stateServiceHostname,
      eventListenerHostname = eventListenerHostname,
      bakerEventListenerHostname = bakerEventListenerHostname,
      skipSetup = skipSetup,
      skipCleanup = skipCleanup
    ))
  }

  def test(specText: String, testTags: Tag*)(runTest: TestContext => IO[Assertion])(implicit pos: source.Position): Unit = {

    val processLogger = ProcessLogger(println(_))

    def exec(command: String): IO[Either[Throwable, String]] =
      IO(command.!!(processLogger)).attempt

    val deleteEnvironment: IO[Either[Throwable, String]] =
      exec(s"kubectl delete -f ${getClass.getResource("/kubernetes").getPath}")

    val createEnvironment: IO[Either[Throwable, String]] =
      exec(s"kubectl apply -f ${getClass.getResource("/kubernetes").getPath}")

    it(specText, testTags: _*) { args =>

      def setup[A](f: IO[A]): IO[Unit] =
        if(args.skipSetup) IO.unit else f.void

      def cleanup[A](f: IO[A]): IO[Unit] =
        if(args.skipCleanup) IO.unit else f.void

      val clientResource = BlazeClientBuilder[IO](executionContext).resource
      val exampleAppClient = new ExampleAppClient(clientResource, args.clientAppHostname)

      (for {
        _ <- cleanup(setup(deleteEnvironment))
        _ <- setup(createEnvironment.flatMap(IO.fromEither))
        _ <- within(1.minute, split = 60)(exampleAppClient.ping.map(status => assert(status.code == 200)))
        attempt <- runTest(TestContext(
          clientApp = exampleAppClient
        )).attempt
        _ <- cleanup(setup(deleteEnvironment))
        outcome <- IO.fromEither(attempt)
      } yield outcome)
        .unsafeToFuture()
    }
  }
}
