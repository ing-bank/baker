package com.ing.baker.baas.smoke.k8s

import cats.effect.{IO, Timer}
import com.ing.baker.baas.smoke.k8s.KubernetesCommands.exec
import com.ing.baker.baas.smoke.{prefixGreen, printGreen, within}

import scala.concurrent.duration._
import scala.sys.process._

case class Pod(name: String, namespace: Namespace) {

  def status: IO[String] =
    IO(s"kubectl get pod $name -n $namespace".!!)

  def ready(implicit timer: Timer[IO]): IO[Unit] =
    status.map(s => assert(s.contains("1/1")))
}

object Pod {

  private val podStatus = ".*(\\d+)/(\\d+).*".r

  private def podsComplete(str: String): Boolean = podStatus.findAllMatchIn(str).collect(
      { case m => m.group(1).toInt == m.group(2).toInt }
    ).forall(identity)

  def printPodsStatuses(namespace: Namespace): IO[Int] =
    exec(
      prefix = prefixGreen("pods"),
      command = s"kubectl get pods -o wide -n $namespace")

  def countPodsWithLabel(label: (String, String), namespace: Namespace): IO[Int] = {
    val (key, value) = label
    for {
      pods <- IO(s"kubectl get pods -l $key=$value -n $namespace".!!)
    } yield pods.split("\n").tail.length
  }

  def allPodsAreReady(namespace: Namespace)(implicit timer: Timer[IO]): IO[Unit] =
    for {
      pods <- IO(s"kubectl get pods -n $namespace".!!)
      _ = assert(podsComplete(pods))
    } yield()

  private val setupWaitTime = 1.minute

  private val setupWaitSplit = 10

  def awaitForAllPods(namespace: Namespace)(implicit timer: Timer[IO]): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- printGreen(s"\nWaiting for bakery cluster (5s)...")
      _ <- Pod.printPodsStatuses(namespace)
      _ <- Pod.allPodsAreReady(namespace)
    } yield ())
}
