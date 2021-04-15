package com.ing.bakery.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.smoke.k8s.{DefinitionFile, Namespace, Pod}
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext

object BakeryEnvironment {

  case class Context(
    clientApp: ExampleAppClient,
    namespace: Namespace
  )

  case class Arguments(
    clientAppHostname: Uri
  )

  def configMapNamespace(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
      namespace <- Namespace.resource
      _ <- Resource.eval(printGreen("\nCreating Bakery cluster environment for configmaps"))
      _ <- DefinitionFile.resource("cassandra.yaml", namespace)
      _ <- DefinitionFile.resource("configmap/bakery-controller.yaml", namespace)
      _ <- DefinitionFile.resource("example-config.yaml", namespace)
      _ <- DefinitionFile.resource("kafka-event-sink.yaml", namespace)
      _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))

      _ <- Resource.eval(printGreen("\nAdding custom resources: interactions, listeners, recipe"))
      _ <- DefinitionFile.resource("configmap/interactions-example.yaml", namespace)
      _ <- DefinitionFile.resource("configmap/baker-webshop.yaml", namespace)
      _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
      _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))
    } yield namespace

  def crdNamespace(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
    namespace <- Namespace.resource
    _ <- Resource.eval(printGreen("\nCreating Bakery cluster environment for CRD"))
    _ <- DefinitionFile.resource("crd/crd-baker.yaml")
    _ <- DefinitionFile.resource("crd/crd-interaction.yaml")
    _ <- DefinitionFile.resource("cassandra.yaml", namespace)
    _ <- DefinitionFile.resource("crd/bakery-controller.yaml", namespace)
    _ <- DefinitionFile.resource("example-config.yaml", namespace)
    _ <- DefinitionFile.resource("kafka-event-sink.yaml", namespace)
    _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))

    _ <- Resource.eval(printGreen("\nAdding custom resources: interactions, listeners, recipe"))
    _ <- DefinitionFile.resource("crd/interactions-example.yaml", namespace)
    _ <- DefinitionFile.resource("crd/baker-webshop.yaml", namespace)
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
    _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))
  } yield namespace

  def unifiedNamespace(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
      namespace <- Namespace.resource
      _ <- Resource.eval(printGreen("Bakery webshop"))
      _ <- DefinitionFile.resource("cassandra.yaml", namespace)
      _ <- DefinitionFile.resource("kafka-event-sink.yaml", namespace)
      _ <- DefinitionFile.resource("external-interactions.yaml", namespace)

      _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))
      _ <- DefinitionFile.resource("webshop-baker.yaml", namespace)
      _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
      _ <- Resource.eval(Pod.waitUntilAllPodsAreReady(namespace))

    }  yield namespace

  def resource(args: Arguments, namespaceSetup: => Resource[IO, Namespace])(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- namespaceSetup
    client <- BlazeClientBuilder[IO](connectionPool).resource
    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)
  } yield Context(
    clientApp = exampleAppClient,
    namespace
  )
}
