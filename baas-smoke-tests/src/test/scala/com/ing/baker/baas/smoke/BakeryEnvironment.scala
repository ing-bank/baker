package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, KubernetesCommands, Namespace, Pod}
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext

object BakeryEnvironment {

  case class Context(
    clientApp: ExampleAppClient,
    namespace: Namespace
  )

  case class Arguments(
    clientAppHostname: Uri,
    eventListenerHostname: Uri,
    bakerEventListenerHostname: Uri
  )

  def resource(args: Arguments)(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- KubernetesCommands.basicSetup

    _ <- Resource.liftF(printGreen(s"\nAdding custom resources: interactions, listeners, recipe"))
    _ <- DefinitionFile.resource("interactions-example.yaml", namespace)
    _ <- DefinitionFile.resource("baker-webshop.yaml", namespace)
    _ <- Resource.liftF(Pod.awaitForAllPods(namespace))

    _ <- Resource.liftF(printGreen(s"\nCreating client app"))
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
    _ <- Resource.liftF(Pod.awaitForAllPods(namespace))

    client <- BlazeClientBuilder[IO](connectionPool).resource
    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
  } yield Context(
    clientApp = exampleAppClient,
    namespace
  )
}
