package com.ing.baker.runtime.core.actor.downing

trait Strategy {
  def sbrDecision(clusterHelper: ClusterHelper)
}
