package com.ing.baker.playground.commands

import cats.implicits._
import com.ing.baker.playground.AppUtils.{App, addRunningImage}
import com.ing.baker.playground.commands.Docker.networkName

object EnvSystems {

  def cassandraName: String = "baker-cassandra"

  def haproxyName: String = "baker-haproxy"

  def runCassandra: App[Unit] =
    Terminal.execAndWait(
      command = s"docker run --name $cassandraName --network $networkName -p 9042:9042 -p 9160:9160 cassandra:latest",
      prompt = "Cassandra",
      condition = _.matches("""INFO  \[OptionalTasks:1\] (.+) CassandraRoleManager\.java:372 - Created default superuser role 'cassandra'""")
    ) *>
    addRunningImage(cassandraName)

  def runHaproxy: App[Unit] =
    Terminal.execAndWait(
      command = s"docker run --name $haproxyName --network $networkName ${BaaS.haproxyStateNodesImage}",
      prompt = "HAProxy",
      condition = _ => true
    ) *>
    addRunningImage(haproxyName)
}
