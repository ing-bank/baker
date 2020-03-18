package com.ing.baker.baas.smoke.k8s

import cats.effect.{IO, Timer}
import com.ing.baker.baas.smoke.k8s.KubernetesCommands.exec
import com.ing.baker.baas.smoke.prefixGreen

import scala.sys.process._

case class Pod(name: String, namespace: Namespace) {

  def status: IO[String] =
    IO(s"kubectl get pod $name -n $namespace".!!)

  def ready(implicit timer: Timer[IO]): IO[Unit] =
    status.map(s => assert(s.contains("1/1")))
}

object Pod {

  def printPodsStatuses(namespace: Namespace): IO[Int] =
    exec(
      prefix = prefixGreen("pods"),
      command = s"kubectl get pods -n $namespace")

  def countPodsWithLabel(label: (String, String), namespace: Namespace): IO[Int] = {
    val (key, value) = label
    for {
      pods <- IO(s"kubectl get pods -l $key=$value -n $namespace".!!)
    } yield pods.split("\n").tail.length
  }

  def allPodsAreReady(namespace: Namespace)(implicit timer: Timer[IO]): IO[Unit] =
    for {
      pods <- IO(s"kubectl get pods -n $namespace".!!)
      _ = assert(!pods.contains("0/1") && pods.contains("1/1"))
    } yield()
}
