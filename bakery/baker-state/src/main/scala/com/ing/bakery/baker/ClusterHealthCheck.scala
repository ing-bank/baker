package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.cluster.{Cluster, MemberStatus}

import scala.concurrent.Future

class ClusterHealthCheck(system: ActorSystem) extends (() => Future[Boolean]) {
  private val cluster = Cluster(system)
  override def apply(): Future[Boolean] = {
    Future.successful(cluster.selfMember.status == MemberStatus.Up)
  }
}
