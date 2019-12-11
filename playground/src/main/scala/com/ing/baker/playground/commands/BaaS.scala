package com.ing.baker.playground.commands

import cats.implicits._
import com.ing.baker.playground.AppUtils._
import Docker.{createDockerNetwork, networkName}

object BaaS {

  val baasVersion = "3.0.2-SNAPSHOT"

  val haproxyStateNodesImage = "playground-haproxy-state-nodes:latest"

  def startBaaS: App[Unit] =
    for {
      _ <- createDockerNetwork
      _ <- EnvSystems.runCassandra
      node1 <- runStateNode(baasVersion, 1, "self")
      _ <- EnvSystems.runHaproxy
      _ <- runInteractionNode(baasVersion, 1, node1)
      _ <- runEventListenerNode(baasVersion, 1, node1)
      _ <- runClientApp(baasVersion, 1, "http://" + EnvSystems.haproxyName + ":8080")
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
    val cmd = s"docker run --name $containerName --network $networkName $envVars baas-node-state:$version"
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

  def runInteractionNode(version: String, node: Int, seedHost: String): App[String] = {
    val containerName: String = s"interaction-node-$node"
    val seedHostname: String = if(seedHost == "self") containerName else seedHost
    val envVars = Map(
      "CLUSTER_HOST" -> containerName,
      "CLUSTER_SEED_HOST" -> seedHostname
    )
      .map { case (env, value) => s"-e $env=$value"}
      .mkString(" ")
    val cmd = s"docker run --name $containerName --network $networkName $envVars baas-interactions-example:$version"
    for {
      _ <- Terminal.execAndWait(
        command = cmd,
        prompt = s"interactions-node:$version:$node",
        condition = _ => true
      )
      _ <- addRunningImage(containerName)
    } yield containerName
  }

  def runEventListenerNode(version: String, node: Int, seedHost: String): App[String] = {
    val containerName: String = s"event-listener-node-$node"
    val seedHostname: String = if(seedHost == "self") containerName else seedHost
    val envVars = Map(
      "CLUSTER_HOST" -> containerName,
      "CLUSTER_SEED_HOST" -> seedHostname
    )
      .map { case (env, value) => s"-e $env=$value"}
      .mkString(" ")
    val cmd = s"docker run --name $containerName --network $networkName $envVars baas-event-listener-example:$version"
    for {
      _ <- Terminal.execAndWait(
        command = cmd,
        prompt = s"event-listener-node:$version:$node",
        condition = _ => true
      )
      _ <- addRunningImage(containerName)
    } yield containerName
  }

  def runClientApp(version: String, node: Int, baasHostname: String): App[String] = {
    val containerName: String = s"client-app-$node"
    val envVars = Map(
      "BAAS_HOSTNAME" -> baasHostname
    )
      .map { case (env, value) => s"-e $env=$value"}
      .mkString(" ")
    val cmd = s"docker run --name $containerName --network $networkName $envVars -p 8080:8080 baas-client-example:$version"
    for {
      _ <- Terminal.execAndWait(
        command = cmd,
        prompt = s"client-app:$version:$node",
        condition = _ => true
      )
      _ <- addRunningImage(containerName)
    } yield containerName
  }

  def buildStateNodesHAProxyImage: App[Unit] =
    Terminal.moveToBakerLocation *> Docker.buildImage(
      "./playground/src/main/resources/haproxy-state-nodes",
      haproxyStateNodesImage
    )
}
