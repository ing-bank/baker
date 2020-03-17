package com.ing.baker.baas.smoke

import java.util.UUID

import cats.syntax.apply._
import cats.syntax.functor._
import cats.effect.{ContextShift, IO, Resource, Timer}
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import scala.sys.process._

object BakeryEnvironment {

  case class Context(
    clientApp: ExampleAppClient,
    recipeEventListener: EventListenerClient,
    bakerEventListener: EventListenerClient
  )

  case class Arguments(
    clientAppHostname: Uri,
    stateServiceHostname: Uri,
    eventListenerHostname: Uri,
    bakerEventListenerHostname: Uri
  )

  def resource(args: Arguments)(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- Resource.make(createNamespace)(deleteNamespace)

    _ <- DefinitionFile.resource("crd-recipe.yaml")
    _ <- DefinitionFile.resource("bakery-controller.yaml", namespace)

    _ <- Resource.liftF(IO.sleep(3.second))
    _ <- Resource.liftF(IO(println(Console.GREEN + s"\nAdding custom resources: interactions, listeners, recipe" + Console.RESET)))

    _ <- DefinitionFile.resource("example-interactions.yaml", namespace)
    _ <- DefinitionFile.resource("example-listeners.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-webshop.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-reservation.yaml", namespace)

    client <- BlazeClientBuilder[IO](connectionPool).resource
    _ <- Resource.liftF(awaitForStateNodes(client, namespace, args))
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)

    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
    recipeEventsClient = new EventListenerClient(client, args.eventListenerHostname)
    bakerEventsClient = new EventListenerClient(client, args.bakerEventListenerHostname)

    _ <- Resource.liftF(awaitForClientApp(exampleAppClient, namespace))
  } yield Context(
    clientApp = exampleAppClient,
    recipeEventListener = recipeEventsClient,
    bakerEventListener = bakerEventsClient
  )

  private def getPathSafe(resourcePath: String): String = {
    val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
    val safePath = getClass.getResource(resourcePath).getPath
    if (isWindows) safePath.tail
    else safePath
  }

  private def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

  private def exec(prefix: String, command: String): IO[Int] = {

    def processLogger(prefix: String): ProcessLogger = ProcessLogger(
      line => println(prefix + " " + line),
      err => stderr.println(Console.RED + err + Console.RESET))

    IO(command.!(processLogger(prefix)))
  }

  private val createNamespace: IO[String] = {
    for {
      testUUID <- IO(UUID.randomUUID().toString)
      prefix = s"[${Console.GREEN}creating env $testUUID${Console.RESET}]"
      _ <- exec(prefix, command = s"kubectl create namespace $testUUID")
    } yield testUUID
  }

  private def deleteNamespace(namespace: String): IO[Unit] = {
    val prefix = s"[${Console.CYAN}cleaning env $namespace${Console.RESET}]"
    for {
      pods <- IO(s"kubectl get pods -n $namespace".!!)
      services <- IO(s"kubectl get services -n $namespace".!!)
      deployments <- IO(s"kubectl get deployments -n $namespace".!!)
      replicasets <- IO(s"kubectl get replicasets -n $namespace".!!)
      _= assert(!pods.contains("Running"), "There were still running pods while deleting namespace")
      _= assert(services == "", "Services where still up while deleting namespace")
      _= assert(deployments == "", "Deployments where still up while deleting namespace")
      _= assert(replicasets == "", "replica sets where still up while deleting namespace")
      _ <- exec(
        prefix = prefix,
        command = s"kubectl delete namespace $namespace"
      )
    } yield Unit

  }

  case class DefinitionFile(path: String, namespace: Option[String])

  object DefinitionFile {

    def resource(path: String, namespace: String)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
      Resource.make(applyFileResource(path, Some(namespace)))(deleteFileResource)
    }

    def resource(path: String)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
      Resource.make(applyFileResource(path, None))(deleteFileResource)
    }

    private def applyFileResource(path: String, namespace: Option[String]): IO[DefinitionFile] = {
      val kubernetesConfigPath = getPathSafe("/kubernetes")
      val prefix = s"[${Console.GREEN}applying file $path $namespace${Console.RESET}]"
      exec(prefix, command = s"kubectl apply -f $kubernetesConfigPath/$path ${namespace.fold("")(ns => "-n " + ns)}")
        .map(_ => DefinitionFile(path, namespace))
    }

    private def deleteFileResource(definitionFile: DefinitionFile)(implicit timer: Timer[IO]): IO[Unit] = {
      val kubernetesConfigPath = getPathSafe("/kubernetes")
      val prefix = s"[${Console.CYAN}deleting file ${definitionFile.path} ${definitionFile.namespace}${Console.RESET}]"
      exec(prefix, command = s"kubectl delete -f $kubernetesConfigPath/${definitionFile.path} ${definitionFile.namespace.fold("")(ns => "-n " + ns)}").void
    }
  }

  private def getPods(namespace: String): IO[Int] =
    exec(
      prefix = s"[${Console.GREEN}pods${Console.RESET}]",
      command = s"kubectl get pods -n $namespace")

  private val setupWaitTime = 1.minute

  private val setupWaitSplit = 60

  def awaitForStateNodes(client: Client[IO], namespace: String, args: Arguments)(implicit timer: Timer[IO]): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- IO(println(Console.GREEN + s"\nWaiting for bakery cluster (5s)..." + Console.RESET))
      _ <- getPods(namespace)
      status <- client.statusFromUri(args.stateServiceHostname / "api" / "v3" / "getAllRecipes")
    } yield assert(status.code == 200))

  def awaitForClientApp(exampleAppClient: ExampleAppClient, namespace: String)(implicit timer: Timer[IO]): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- IO(println(Console.GREEN + s"\nWaiting for client app (5s)..." + Console.RESET))
      _ <- getPods(namespace)
      status <- exampleAppClient.ping
    } yield assert(status.code == 200))

}
