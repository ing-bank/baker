package com.ing.baker.baas.smoke

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.k8s.{KubernetesCommands, LogInspectionService, Namespace}

object BakeryControllerEnvironment {

  case class Context(namespace: Namespace, inspector: LogInspectionService.Inspector)

  case class Arguments(debugMode: Boolean)

  def resource(args: Arguments)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- KubernetesCommands.basicSetup
    inspector <- LogInspectionService.resource(
      testsName = "Bakery Controller",
      hostname = InetSocketAddress.createUnresolved("0.0.0.0", 9000),
      awaitLock = args.debugMode)
    _ <- Resource.liftF(inspector.watchLogs("bakery-controller", None, namespace))
  } yield Context(namespace, inspector)
}
