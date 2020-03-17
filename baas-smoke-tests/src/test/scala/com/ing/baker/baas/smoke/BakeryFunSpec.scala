package com.ing.baker.baas.smoke

import java.util.UUID

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalactic.source
import org.scalatest.compatible.Assertion
import org.scalatest.{FutureOutcome, Tag, fixture}

import scala.concurrent.duration._
import scala.sys.process._

abstract class BakeryFunSpec extends fixture.AsyncFunSpecLike {

  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(executionContext)

  implicit val timer: Timer[IO] =
    IO.timer(executionContext)

  val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))

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
                          clientApp: ExampleAppClient,
                          recipeEventListener: EventListenerClient,
                          bakerEventListener: EventListenerClient
                        )

  case class TestArguments(
                            clientAppHostname: Uri,
                            stateServiceHostname: Uri,
                            eventListenerHostname: Uri,
                            bakerEventListenerHostname: Uri,
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
    val skipCleanup = {
      val skipCleanup = test.configMap.getOptional[String]("skip-cleanup").getOrElse("false")
      skipCleanup == "true" || skipCleanup == "t" || skipCleanup == "1" || skipCleanup == "yes"
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

    it(specText, testTags: _*) { args =>


      /*
      def dontSkipTest: IO[Assertion] =

        for {
          namespace <- setup(createEnvironment)
          outcome <- BlazeClientBuilder[IO](executionContext).resource.use { client =>

            for {
              _ <- IO(println(Console.GREEN + s"\nSetting up Bakery environment" + Console.RESET))
              _ <- setup(applyFile("crd-recipe.yaml", namespace.getOrElse("default")))
              _ <- setup(applyFile("bakery-controller.yaml", namespace.getOrElse("default")))
              _ <- IO.sleep(3.second)

              _ <- IO(println(Console.GREEN + s"\nAdding custom resources: interactions, listeners, recipe" + Console.RESET))
              _ <- setup(applyFile("example-interactions.yaml", namespace.getOrElse("default")))
              _ <- setup(applyFile("example-listeners.yaml", namespace.getOrElse("default")))
              _ <- setup(applyFile("recipe-webshop.yaml", namespace.getOrElse("default")))

              _ <- within(setupWaitTime, setupWaitSplit)(for {
                _ <- IO(println(Console.GREEN + s"\nWaiting for bakery cluster (5s)..." + Console.RESET))
                _ <- getPods(namespace)
                status <- client.statusFromUri(args.stateServiceHostname / "api" / "v3" / "getAllRecipes")
              } yield assert(status.code == 200))
              _ <- setup(applyFile("example-client-app.yaml", namespace.getOrElse("default")))
              _ <- within(setupWaitTime, setupWaitSplit)(for {
                _ <- IO(println(Console.GREEN + s"\nWaiting for client app (5s)..." + Console.RESET))
                _ <- getPods(namespace)
                status <- exampleAppClient.ping
              } yield assert(status.code == 200))
              attempt <- runTest(TestContext(
                clientApp = exampleAppClient,
                recipeEventListener = recipeEventsClient,
                bakerEventListener = bakerEventsClient
              )).attempt
              _ <- cleanup(deleteEnvironment(namespace))
              outcome <- IO.fromEither(attempt)
            } yield outcome
          }
        } yield outcome

      def skipTest: IO[Assertion] =
        IO(println(Console.YELLOW + "Skipping the smoke test because 'kubectl' command not available..." + Console.RESET)) *> IO.pure(succeed)

      (for {
        canRun <- kubernetesAvailable
        outcome <- if (canRun) dontSkipTest else skipTest
      } yield outcome).unsafeToFuture()
      */

      environmentResource.use(runTest(_)).unsafeToFuture()
    }
  }
}
