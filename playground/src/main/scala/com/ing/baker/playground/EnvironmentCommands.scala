package com.ing.baker.playground

import cats.implicits._
import com.ing.baker.playground.Command.execPrintAndWaitForMatch
import com.ing.baker.playground.DockerCommands.networkName
import AppMonad._

import scala.sys.process.Process

object EnvironmentCommands {

  def cassandraName: String = "baker-cassandra"

  def haproxyName: String = "baker-haproxy"

  def runCassandra: App[Unit] =
    execPrintAndWaitForMatch(
      process = Process(s"docker run --name $cassandraName --network $networkName -p 9042:9042 -p 9160:9160 cassandra:latest"),
      prompt = "Cassandra",
      condition = _.matches("""INFO  \[OptionalTasks:1\] (.+) CassandraRoleManager\.java:372 - Created default superuser role 'cassandra'""")
    ).app *>
    addRunningImage(cassandraName)

  def runHaproxy: App[Unit] =
    execPrintAndWaitForMatch(
      process = Process(s"docker run --name $haproxyName --network $networkName -p 8080:8080 baker-haproxy:latest"),
      prompt = "HAProxy",
      condition = _ => true
    ).app *>
    addRunningImage(haproxyName)
}
