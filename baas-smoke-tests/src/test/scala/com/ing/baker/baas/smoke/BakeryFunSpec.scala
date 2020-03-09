package com.ing.baker.baas.smoke

import java.util.UUID

import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import org.http4s.Uri
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

    it(specText, testTags: _*) { args =>

      def setup[A](f: IO[A]): IO[Option[A]] =
        if(args.skipSetup) IO.pure(None) else f.map(Some(_))

      def cleanup[A](f: IO[A]): IO[Unit] =
        if(args.skipCleanup) IO.unit else f.void

      def processLogger(prefix: String): ProcessLogger = ProcessLogger(
        line => println(prefix + " " + line),
        err => stderr.println(Console.RED + err + Console.RESET))

      def exec(prefix: String, command: String): IO[Int] =
        IO(command.!(processLogger(prefix)))

      val kubernetesAvailable: IO[Boolean] =
        IO("kubectl --help".!(ProcessLogger(_ => ())) == 0)

      def deleteEnvironment(namespaceOpt: Option[String]): IO[Int] = {
        namespaceOpt match {
          case Some(namespace) =>
            val prefix = s"[${Console.CYAN}cleaning env $namespace${Console.RESET}]"
            exec(
              prefix = prefix,
              command = s"kubectl delete -f ${getClass.getResource("/kubernetes").getPath} -n $namespace"
            ) *> exec(
              prefix = prefix,
              command = s"kubectl delete namespace $namespace"
            )
          case None =>
            IO(println(Console.YELLOW + "### Skipping cleanup because we skipped startup" + Console.RESET)) *> IO.pure(0)
        }
      }

      val createEnvironment: IO[String] = {
        for {
          testUUID <- IO( UUID.randomUUID().toString )
          kubernetesConfigPath = getClass.getResource("/kubernetes").getPath
          prefix = s"[${Console.GREEN}creating env $testUUID${Console.RESET}]"
          _ <- exec(prefix, command = s"kubectl create namespace $testUUID")
          _ = if(args.skipCleanup) {
            println(Console.YELLOW + s"### Will skip cleanup after the test, to manually clean the environment run: " + Console.RESET)
            println(s"\n\tkubectl delete -f $kubernetesConfigPath -n $testUUID && kubectl delete namespace $testUUID\n")
          }
        } yield testUUID
      }

      def applyFile(name: String, namespace: String): IO[Unit] = {
        val kubernetesConfigPath = getClass.getResource("/kubernetes").getPath
        val prefix = s"[${Console.GREEN}applying file $name $namespace${Console.RESET}]"
        exec(prefix, command = s"kubectl apply -f $kubernetesConfigPath/$name -n $namespace").void
      }

      def getPods(namespaceOpt: Option[String]): IO[Int] =
        namespaceOpt match {
          case Some(namespace) =>
            exec(
              prefix = s"[${Console.GREEN}pods${Console.RESET}]",
              command = s"kubectl get pods -n $namespace")
          case None =>
            IO( println(Console.GREEN + "Skipped startup, will run the tests immediately" + Console.RESET)) *> IO.pure(0)
        }


      val setupWaitTime = 5.minute
      val setupWaitSplit = 60

      def dontSkipTest: IO[Assertion] =
        for {
          namespace <- setup(createEnvironment)
          outcome <- BlazeClientBuilder[IO](executionContext).resource.use { client =>
            val exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
            val recipeEventsClient = new EventListenerClient(client, args.eventListenerHostname)
            val bakerEventsClient = new EventListenerClient(client, args.bakerEventListenerHostname)
            for {
              _ <- setup(applyFile("example-interactions.yaml", namespace.getOrElse("default")))
              _ <- setup(applyFile("example-listeners.yaml", namespace.getOrElse("default")))
              _ <- setup(applyFile("bakery-cluster.yaml", namespace.getOrElse("default")))
              _ <- within(setupWaitTime, setupWaitSplit)(for {
                _ <- IO ( println(Console.GREEN + s"\nWaiting for bakery cluster (5s)..." + Console.RESET) )
                _ <- getPods(namespace)
                status <- client.statusFromUri(args.stateServiceHostname / "api" / "v3" / "getAllRecipes")
              } yield assert(status.code == 200))
              _ <- setup(applyFile("example-client-app.yaml", namespace.getOrElse("default")))
              _ <- within(setupWaitTime, setupWaitSplit)(for {
                _ <- IO ( println(Console.GREEN + s"\nWaiting for client app (5s)..." + Console.RESET) )
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
    }
  }
}
