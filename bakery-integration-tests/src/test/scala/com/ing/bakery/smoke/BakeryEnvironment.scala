package com.ing.bakery.smoke

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.smoke.k8s.{DefinitionFile, LogInspectionService, Namespace, Pod}
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder

import scala.concurrent.ExecutionContext

object BakeryEnvironment {

  case class Context(
    clientApp: ExampleAppClient,
    namespace: Namespace,
    inspector: LogInspectionService.Inspector
  )

  case class Arguments(
    clientAppHostname: Uri,
    debugMode: Boolean
  )

  def configMapNamespace(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
      namespace <- Namespace.resource
      _ <- Resource.liftF(printGreen("\nCreating Bakery cluster environment for configmaps"))
      _ <- DefinitionFile.resource("cassandra.yaml", namespace)
      _ <- DefinitionFile.resource("configmap/bakery-controller.yaml", namespace)
      _ <- DefinitionFile.resource("example-config.yaml", namespace)
      _ <- DefinitionFile.resource("kafka-event-sink.yaml", namespace)
      _ <- Resource.liftF(Pod.waitUntilAllPodsAreReady(namespace))

      _ <- Resource.liftF(printGreen("\nAdding custom resources: interactions, listeners, recipe"))
      _ <- DefinitionFile.resource("configmap/interactions-example.yaml", namespace)
      _ <- DefinitionFile.resource("configmap/baker-webshop.yaml", namespace)
      _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
      _ <- Resource.liftF(Pod.waitUntilAllPodsAreReady(namespace))
    } yield namespace

  def crdNamespace(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
    namespace <- Namespace.resource
    _ <- Resource.liftF(printGreen("\nCreating Bakery cluster environment for CRD"))
    _ <- DefinitionFile.resource("crd/crd-baker.yaml")
    _ <- DefinitionFile.resource("crd/crd-interaction.yaml")
    _ <- DefinitionFile.resource("cassandra.yaml", namespace)
    _ <- DefinitionFile.resource("crd/bakery-controller.yaml", namespace)
    _ <- DefinitionFile.resource("example-config.yaml", namespace)
    _ <- DefinitionFile.resource("kafka-event-sink.yaml", namespace)
    _ <- Resource.liftF(Pod.waitUntilAllPodsAreReady(namespace))

    _ <- Resource.liftF(printGreen("\nAdding custom resources: interactions, listeners, recipe"))
    _ <- DefinitionFile.resource("crd/interactions-example.yaml", namespace)
    _ <- DefinitionFile.resource("crd/baker-webshop.yaml", namespace)
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
    _ <- Resource.liftF(Pod.waitUntilAllPodsAreReady(namespace))
  } yield namespace

  def resource(args: Arguments, namespaceSetup: => Resource[IO, Namespace])(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- namespaceSetup
    client <- BlazeClientBuilder[IO](connectionPool).resource
    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)

    inspector <- LogInspectionService.resource(
      testsName = "Bakery Controller",
      hostname = InetSocketAddress.createUnresolved("0.0.0.0", 9090),
      awaitLock = args.debugMode)
    _ <- Resource.liftF(inspector.watchLogs("bakery-controller", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("webshop-baker", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("reserve-items", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("client-app", Some("client-app"), namespace))
  } yield Context(
    clientApp = exampleAppClient,
    namespace,
    inspector
  )
}
