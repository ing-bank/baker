package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, KubernetesCommands, Namespace, Pod}
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext

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
    namespace <- KubernetesCommands.basicSetup

    _ <- Resource.liftF(printGreen(s"\nAdding custom resources: interactions, listeners, recipe"))
    _ <- DefinitionFile.resource("interactions-example.yaml", namespace)
    _ <- DefinitionFile.resource("example-listeners.yaml", namespace)
    _ <- DefinitionFile.resource("recipe-webshop.yaml", namespace)
    _ <- Resource.liftF(Pod.awaitForAllPods(namespace))

    _ <- Resource.liftF(printGreen(s"\nCreating client app"))
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
    _ <- Resource.liftF(Pod.awaitForAllPods(namespace))

    client <- BlazeClientBuilder[IO](connectionPool).resource
    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
    recipeEventsClient = new EventListenerClient(client, args.eventListenerHostname)
    bakerEventsClient = new EventListenerClient(client, args.bakerEventListenerHostname)
  } yield Context(
    clientApp = exampleAppClient,
    recipeEventListener = recipeEventsClient,
    bakerEventListener = bakerEventsClient
  )
}
