package com.ing.baker.baas.smoke.resources

import java.util.UUID

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke.exec
import scala.sys.process._

object Namespace {

  def resource(): Resource[IO, String] = Resource.make(createNamespace)(deleteNamespace)

  private val createNamespace: IO[String] = {
    for {
      testUUID <- IO(UUID.randomUUID().toString)
      prefix = s"[${Console.GREEN}creating env $testUUID${Console.RESET}]"
      _ <- exec(prefix, command = s"kubectl create namespace $testUUID")
    } yield testUUID
  }

  private def deleteNamespace(namespace: String): IO[Unit] = {
    val prefix = s"[${Console.CYAN}cleaning env $namespace${Console.RESET}]"
    for {
      pods <- IO(s"kubectl get pods -n $namespace".!!)
      services <- IO(s"kubectl get services -n $namespace".!!)
      deployments <- IO(s"kubectl get deployments -n $namespace".!!)
      replicasets <- IO(s"kubectl get replicasets -n $namespace".!!)
      _= assert(!pods.contains("Running"), "There were still running pods while deleting namespace")
      _= assert(services == "", "Services where still up while deleting namespace")
      _= assert(deployments == "", "Deployments where still up while deleting namespace")
      _= assert(replicasets == "", "replica sets where still up while deleting namespace")
      _ <- exec(
        prefix = prefix,
        command = s"kubectl delete namespace $namespace"
      )
    } yield Unit
  }
}
