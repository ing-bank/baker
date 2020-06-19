package com.ing.baker.baas.smoke

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, KubernetesCommands, LogInspectionService, Namespace, Pod}
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

  def resource(args: Arguments)(implicit connectionPool: ExecutionContext, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- KubernetesCommands.basicSetup

    _ <- Resource.liftF(printGreen(s"\nAdding custom resources: interactions, listeners, recipe"))
    _ <- DefinitionFile.resource("interactions-example-config-map.yaml", namespace)
    _ <- DefinitionFile.resource("baker-webshop.yaml", namespace)
    _ <- DefinitionFile.resource("example-client-app.yaml", namespace)
    _ <- Resource.liftF(Pod.waitUntilAllPodsAreReady(namespace).attempt.flatMap {
      case Left(_) => printRed("ERROR Pods were not ready on time, will terminate...")
      case Right(_) => IO.unit
    })

    client <- BlazeClientBuilder[IO](connectionPool).resource
    exampleAppClient = new ExampleAppClient(client, args.clientAppHostname)

    inspector <- LogInspectionService.resource(
      testsName = "Bakery Controller",
      hostname = InetSocketAddress.createUnresolved("0.0.0.0", 9090),
      awaitLock = args.debugMode)
    _ <- Resource.liftF(inspector.watchLogs("bakery-controller", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("baas-state", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("reserve-items", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("make-payment-and-ship-items", None, namespace))
    _ <- Resource.liftF(inspector.watchLogsWithPrefix("client-app", Some("client-app"), namespace))
  } yield Context(
    clientApp = exampleAppClient,
    namespace,
    inspector
  )
}
