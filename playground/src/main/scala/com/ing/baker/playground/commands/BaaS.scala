package com.ing.baker.playground.commands

import com.ing.baker.playground.AppUtils._
import Docker.{createDockerNetwork, networkName}

object BaaS {

  val baasStateNodeVersion = "3.0.2-SNAPSHOT"

  def startBaaS: App[Unit] =
    for {
      _ <- createDockerNetwork
      _ <- EnvSystems.runCassandra
      node1 <- runStateNode(baasStateNodeVersion, 1, "self")
      _ <- runStateNode(baasStateNodeVersion, 2, node1)
      _ <- runStateNode(baasStateNodeVersion, 3, node1)
      _ <- EnvSystems.runHaproxy
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
    for {
      _ <- Terminal.execAndWait(
        command = cmd,
        prompt = s"state-node:$version:$node",
        condition = _.contains(s"State Node started...")
      )
      _ <- printLn(s"Node: $containerName successfully started")
      _ <- addRunningImage(containerName)
    } yield containerName
  }

}
