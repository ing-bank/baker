package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.k8s.{KubernetesCommands, Namespace}

object BakeryControllerEnvironment {

  case class Context(namespace: Namespace)

  def resource(args: Unit)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Context] = for {
    namespace <- KubernetesCommands.basicSetup
  } yield Context(namespace)
}
