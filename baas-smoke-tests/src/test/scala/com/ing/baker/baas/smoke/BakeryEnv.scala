package com.ing.baker.baas.smoke

import java.util.UUID

import cats.effect.{IO, Resource}
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.duration.FiniteDuration
import scala.sys.process.{ProcessLogger, stderr}

object BakeryEnv {

  def getPathSafe(resourcePath: String): String = {
    val safePath = getClass.getResource(resourcePath).getPath
    if (isWindows)
      safePath.tail
    else
      safePath
  }

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

  def processLogger(prefix: String): ProcessLogger = ProcessLogger(
    line => println(prefix + " " + line),
    err => stderr.println(Console.RED + err + Console.RESET))

  def exec(prefix: String, command: String): IO[Int] =
    IO(command.!(processLogger(prefix)))

  def deleteEnvironment(namespace: String): IO[Unit] = {
    val prefix = s"[${Console.CYAN}cleaning env $namespace${Console.RESET}]"
    exec(
      prefix = prefix,
      command = s"kubectl delete -f ${getPathSafe("/kubernetes")} -n $namespace"
    ) *> exec(
      prefix = prefix,
      command = s"kubectl delete namespace $namespace"
    ).void
  }

  val createEnvironment: IO[String] = {
    for {

      testUUID <- IO(UUID.randomUUID().toString)
      kubernetesConfigPath = getPathSafe("/kubernetes")

      prefix = s"[${Console.GREEN}creating env $testUUID${Console.RESET}]"
      _ <- exec(prefix, command = s"kubectl create namespace $testUUID")
      _ = if (args.skipCleanup) {
        println(Console.YELLOW + s"### Will skip cleanup after the test, to manually clean the environment run: " + Console.RESET)
        println(s"\n\tkubectl delete -f $kubernetesConfigPath -n $testUUID && kubectl delete namespace $testUUID\n")
      }
    } yield testUUID
  }

  def applyFile(name: String, namespace: String): IO[Unit] = {
    val kubernetesConfigPath = getPathSafe("/kubernetes")
    val prefix = s"[${Console.GREEN}applying file $name $namespace${Console.RESET}]"
    exec(prefix, command = s"kubectl apply -f $kubernetesConfigPath/$name -n $namespace").void

  }

  case class DefinitionFile(path: String,
                            namespace: Option[String])
  object DefinitionFile {
    def resource(path: String, namespace: String): Resource[IO, DefinitionFile] = {
      Resource.make(applyFileResource(path, Some(namespace)))(deleteFileResource)
    }

    def resource(path: String): Resource[IO, DefinitionFile] = {
      Resource.make(applyFileResource(path, None))(deleteFileResource)
    }

    private def applyFileResource(path: String, namespace: Option[String]): IO[DefinitionFile] = {
      val kubernetesConfigPath = getPathSafe("/kubernetes")
      val prefix = s"[${Console.GREEN}applying file $path $namespace${Console.RESET}]"
      exec(prefix, command = s"kubectl apply -f $kubernetesConfigPath/$path ${namespace.fold("")(ns => "-n " + ns)}")
        .map(_ => DefinitionFile(path, namespace))
    }

    private def deleteFileResource(definitionFile: DefinitionFile): IO[Unit] = {
      val kubernetesConfigPath = getPathSafe("/kubernetes")
      val prefix = s"[${Console.CYAN}deleting file ${definitionFile.path} ${definitionFile.namespace}${Console.RESET}]"
      exec(prefix, command = s"kubectl delete -f $kubernetesConfigPath/${definitionFile.path} ${definitionFile.namespace.fold("")(ns => "-n " + ns)}").void
    }
  }

  def getPods(namespace: String): IO[Int] =
    exec(
      prefix = s"[${Console.GREEN}pods${Console.RESET}]",
      command = s"kubectl get pods -n $namespace")

  val setupWaitTime = 1.minute
  val setupWaitSplit = 60

  def awaitForStateNodes(client: Client[IO], namespace: String): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- IO(println(Console.GREEN + s"\nWaiting for bakery cluster (5s)..." + Console.RESET))
      _ <- getPods(namespace)
      status <- client.statusFromUri(args.stateServiceHostname / "api" / "v3" / "getAllRecipes")
    } yield assert(status.code == 200))

  def awaitForClientApp(exampleAppClient: ExampleAppClient, namespace: String): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- IO(println(Console.GREEN + s"\nWaiting for client app (5s)..." + Console.RESET))
      _ <- getPods(namespace)
      status <- exampleAppClient.ping
    } yield assert(status.code == 200))

  val environmentResource = for {
    namespace <- Resource.make(createEnvironment)(deleteEnvironment)

    _ <- DefinitionFile.resource("crd-recipe.yaml")
    _ <- DefinitionFile.resource("bakery-controller.yaml", namespace)

    _ <- Resource.liftF(IO.sleep(3.second))
    _ <- Resource.liftF(IO(println(Console.GREEN + s"\nAdding custom resources: interactions, listeners, recipe" + Console.RESET)))

    _ <- DefinitionFile.resource("example-interactions.yaml", namespace)
    _ <- DefinitionFile.resource("example-listeners.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-webshop.yaml", namespace)

    client <- BlazeClientBuilder[IO](executionContext).resource
    _ <- Resource.liftF(awaitForStateNodes(client, namespace))
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)

    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
    recipeEventsClient = new EventListenerClient(client, args.eventListenerHostname)
    bakerEventsClient = new EventListenerClient(client, args.bakerEventListenerHostname)

    _ <- Resource.liftF(awaitForClientApp(exampleAppClient, namespace))

  } yield TestContext(
    clientApp = exampleAppClient,
    recipeEventListener = recipeEventsClient,
    bakerEventListener = bakerEventsClient
  )
}
