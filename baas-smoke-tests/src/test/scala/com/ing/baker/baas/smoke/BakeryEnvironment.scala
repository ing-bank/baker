package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.syntax.apply._
import com.ing.baker.baas.smoke.resources.{DefinitionFile, Namespace}
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

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
    namespace <-Namespace.resource()
    _ <- Resource.liftF(IO(println(Console.GREEN + s"\nCreating Bakery cluster environment." + Console.RESET)))
    _ <- DefinitionFile.resource("crd-recipe.yaml")
    _ <- DefinitionFile.resource("bakery-controller.yaml", namespace)

    _ <- Resource.liftF(IO.sleep(3.second))
    _ <- Resource.liftF(IO(println(Console.GREEN + s"\nAdding custom resources: interactions, listeners, recipe" + Console.RESET)))

    _ <- DefinitionFile.resource("example-interactions.yaml", namespace)
    _ <- DefinitionFile.resource("example-listeners.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-webshop.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-reservation.yaml", namespace)

    _ <- Resource.liftF(IO(println(Console.GREEN + s"\nCreating client app" + Console.RESET)))
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


  private def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
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
