package com.ing.bakery.smoke.k8s

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.bakery.smoke._
import com.ing.bakery.smoke.k8s.KubernetesCommands.exec

import scala.concurrent.duration._
import scala.sys.process._

case class Pod(name: String, namespace: Namespace) {

  private def output(container: String, command: String, prefix: String)(contents: String) =
    println(s"$command@$container ($prefix): $contents")


  def status: IO[String] =
    IO(s"kubectl get pod $name -n $namespace".!!)

  def ready(implicit timer: Timer[IO]): IO[Unit] =
    status.map(s => assert(s.contains("1/1")))

  def exec(command: String, containerName: Option[String]): IO[String] = {
    val containerOption = containerName.map(id => s"-c $id").getOrElse("")
    val command0 = s"kubectl exec $name -n $namespace $containerOption -- $command"
    IO(command0.!!(ProcessLogger.apply(output(name, command, "out"), output(name, command,"err"))))
  }
}

object Pod {

  val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))

  val splitChar: String = if(isWindows) "\r\n" else "\n"

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
      pods <- IO(s"kubectl get pods --no-headers=true -n $namespace".!!)
      _ = assert(podsComplete(pods))
    } yield()

  private val setupWaitTime = 10.minute

  private val setupWaitSplit = 100

  def waitUntilAllPodsAreReady(namespace: Namespace)(implicit timer: Timer[IO]): IO[Unit] =
    within(setupWaitTime, setupWaitSplit)(for {
      _ <- printGreen(s"\nWaiting for all pods to become active (5s)...")
      _ <- Pod.allPodsAreReady(namespace)
    } yield ()) *> Pod.printPodsStatuses(namespace).void.attempt.flatMap {
    case Left(_) => printRed("ERROR Pods were not ready on time, will terminate...")
    case Right(_) => IO.unit
  }

  def getPodsNames(name: String, namespace: Namespace): IO[List[String]] =
    for {
      pods0<- IO(s"kubectl get --no-headers=true pods -o name -n $namespace".!!).map(_.split(splitChar).toList)
      regex = s"pod\\/($name.+)".r
      pods1 = pods0.mapFilter {
        case regex(podName) => Some(podName)
        case _ => None
      }
    } yield pods1

  def execOnNamed(name: String, namespace: Namespace, containerId: Option[String] = None)(command: String): IO[List[String]] =
    getPodsNames(name, namespace).flatMap(_.traverse({ name0 =>
        Pod(name0, namespace).exec(command, containerId)
          .map(_.split(splitChar).toList)
      }).map(_.flatten) )

  def environmentVariable(name: String, namespace: Namespace)(variableName: String): IO[String] =
    for {
      env <- execOnNamed(name, namespace)("env")
    } yield {
      env
        .find(_.startsWith(s"$variableName="))
        .map(_.reverse.takeWhile(_ != '=').reverse)
        .getOrElse("")
    }
}
