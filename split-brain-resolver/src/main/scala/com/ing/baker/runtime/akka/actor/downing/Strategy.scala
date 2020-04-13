package com.ing.baker.runtime.akka.actor.downing

trait Strategy {
  def sbrDecision(clusterHelper: ClusterHelper): Unit
}
