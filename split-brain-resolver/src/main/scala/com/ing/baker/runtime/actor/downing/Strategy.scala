package com.ing.baker.runtime.actor.downing

trait Strategy {
  def sbrDecision(clusterHelper: ClusterHelper)
}
