package com.ing.baker.baas.smoke.k8s

import cats.implicits._
import cats.effect.{IO, Timer}
import com.ing.baker.baas.smoke.k8s.KubernetesCommands.exec
import com.ing.baker.baas.smoke._

import scala.concurrent.duration._
import scala.sys.process._

case class Pod(name: String, namespace: Namespace) {

  def status: IO[String] =
    IO(s"kubectl get pod $name -n $namespace".!!)

  def ready(implicit timer: Timer[IO]): IO[Unit] =
    status.map(s => assert(s.contains("1/1")))

  def exec(command: String): IO[String] = {
    val command0 = s"kubectl exec $name -n $namespace -- $command"
    IO(command0.!!(ProcessLogger.apply(_ => Unit, _ => Unit)))
  }
}

object Pod {

  val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))

  val splitChar: String = if(isWindows) "\r\n" else "\n"

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
      pods <- IO(s"kubectl get pods --no-headers=true -n $namespace".!!)
      podsLines = pods.split(splitChar).toList
      _ = assert(!podsLines.exists(_.contains("0/1")) && podsLines.forall(_.contains("1/1")))
    } yield()

  private val setupWaitTime = 1.minute

  private val setupWaitSplit = 10

  def awaitForAllPods(namespace: Namespace)(implicit timer: Timer[IO]): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- printGreen(s"\nWaiting for bakery cluster (5s)...")
      _ <- Pod.printPodsStatuses(namespace)
      _ <- Pod.allPodsAreReady(namespace)
    } yield ())

  def getPodsNames(name: String, namespace: Namespace): IO[List[String]] =
    for {
      pods0<- IO(s"kubectl get --no-headers=true pods -o name -n $namespace".!!).map(_.split(splitChar).toList)
      regex = s"pod\\/($name.+)".r
      pods1 = pods0.mapFilter {
        case regex(podName) => Some(podName)
        case _ => None
      }
    } yield pods1

  def execOnNamed(name: String, namespace: Namespace)(command: String): IO[List[List[String]]] =
    getPodsNames(name, namespace).flatMap(_
      .traverse { name0 =>
        Pod(name0, namespace).exec(command)
          .map(_.split(splitChar).toList)
      })
}
