package com.ing.baker.baas.smoke.k8s

import java.util.UUID

import com.ing.baker.baas.smoke.prefixGreen
import cats.effect.{IO, Resource}
import cats.syntax.functor._

case class Namespace(value: String) extends AnyVal {

  def delete: IO[Unit] = {
    val prefix = s"[${Console.CYAN}cleaning env $value${Console.RESET}]"
    KubernetesCommands.exec(
      prefix = prefix,
      command = s"kubectl delete namespace $value"
    ).void
  }

  override def toString: String = value
}

object Namespace {

  def apply: IO[Namespace] = {
    for {
      testUUID <- IO(UUID.randomUUID().toString)
      _ <- KubernetesCommands.exec(
        prefix = prefixGreen(s"creating env $testUUID"),
        command = s"kubectl create namespace $testUUID")
    } yield Namespace(testUUID)
  }

  def resource: Resource[IO, Namespace] = Resource.make(apply)(_.delete)
}
