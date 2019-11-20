package com.ing.baker.playground

import scala.sys.process._
import DockerCommands._
import Command._
import AppMonad._

object BaaSCommands {

  val baasStateNodeVersion = "3.0.2-SNAPSHOT"

  def startBaaS: App[Unit] =
    for {
      _ <- createDockerNetwork
      _ <- EnvironmentCommands.runCassandra
      node1 <- runStateNode(baasStateNodeVersion, 1, "self")
      node2 <- runStateNode(baasStateNodeVersion, 2, node1)
      node3 <- runStateNode(baasStateNodeVersion, 3, node1)
      _ <- EnvironmentCommands.runHaproxy
    } yield ()

  def runStateNode(version: String, node: Int, seedHost: String): App[String] = {
    val containerName: String = s"state-node-$node"
    val seedHostname: String = if(seedHost == "self") containerName else seedHost
    val envVars = Map(
      "CLUSTER_HOST" -> containerName,
      "CLUSTER_SEED_HOST" -> seedHostname,
      "CASSANDRA_CONTACT_POINTS_0" -> "baker-cassandra"
    )
      .map { case (env, value) => s"-e $env=$value"}
      .mkString(" ")
    val cmd = s"docker run --name $containerName --network $networkName $envVars apollo.docker.ing.net/baas-node-state:$version"
    val runNode = execPrintAndWaitForMatch(
      process = Process(cmd),
      prompt = s"state-node:$version:$node",
      condition = _.contains(s"State Node started...")
    ).map(_ => containerName)
    for {
      nodeName <- runNode.app
      _ <- printLn(s"Node: $nodeName successfully started")
      _ <- addRunningImage(nodeName)
    } yield nodeName
  }

}
