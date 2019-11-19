package com.ing.baker.playground

import cats.effect.{ExitCode, IO, IOApp}

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {
    PlaygroundApp.loop.map(_ => ExitCode.Success)
  }

  /*
  def baasBasicCluster: IO[Unit] = {
    val baasStateNodeVersion = "3.0.2-SNAPSHOT"
    scenario {
      for {
        //_ <- dockerPullStateNode(baasStateNodeVersion)
        node1 <- runStateNode(baasStateNodeVersion, 1, "self")
        node2 <- runStateNode(baasStateNodeVersion, 2, node1)
        node3 <- runStateNode(baasStateNodeVersion, 3, node1)
        _ <- IO { scala.io.StdIn.readLine() }
        _ <- terminate(node1)
        _ <- terminate(node2)
        _ <- terminate(node3)
      } yield ()
    }
  }

  def scenario(program: IO[Unit]): IO[Unit] =
    for {
      _ <- dockerIsRequiredVersion
      _ <- createEnvironment.bracket(_ => program)(cleanEnvironment)
    } yield ()

  case class Environment(cassandra: Process, haproxy: Process)

  def createEnvironment: IO[Environment] =
    for {
      _ <- terminateHaproxy
      _ <- terminateCassandra
      _ <- createDockerNetwork
      //_ <- dockerPullCassandra
      //_ <- dockerPullHaproxy
      haproxy <- runHaproxy
      cassandra <- runCassandra
    } yield Environment(cassandra, haproxy)

  def cleanEnvironment(env: Environment): IO[Unit] =
    for {
      _ <- terminateHaproxy
      _ <- terminateCassandra
      _ <- deleteDockerNetwork
    } yield ()
  */

  /*
  def networkName: String = "baker-playground-network"

  def runCassandra: IO[Process] =
    execPrintAndWaitForMatch(
      process = Process(s"docker run --name baker-cassandra --network $networkName -p 9042:9042 -p 9160:9160 cassandra:latest"),
      prompt = "Cassandra",
      condition = _.matches("""INFO  \[OptionalTasks:1\] (.+) CassandraRoleManager\.java:372 - Created default superuser role 'cassandra'""")
    )

  def runHaproxy: IO[Process] =
    execPrintAndWaitForMatch(
      process = Process(s"docker run --name baker-haproxy --network $networkName -p 8080:8080 baker-haproxy:latest"),
      prompt = "Haproxy",
      condition = _ => true
    )

  def runStateNode(version: String, node: Int, seedHost: String): IO[String] = {
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
    execPrintAndWaitForMatch(
      process = Process(cmd),
      prompt = s"state-node:$version:$node",
      condition = _.contains(s"State Node started...")
    ).map(_ => containerName)
  }

  def terminateHaproxy: IO[Unit] =
    terminate("baker-haproxy")

  def dockerPullCassandra: IO[Unit] =
    dockerPull("cassandra")

  def dockerPullHaproxy: IO[Unit] =
    dockerPull("apollo.docker.ing.net/baker-haproxy:latest")

  def dockerPullStateNode(version: String): IO[Unit] =
    dockerPull(s"apollo.docker.ing.net/baas-node-state:$version")
   */

}
