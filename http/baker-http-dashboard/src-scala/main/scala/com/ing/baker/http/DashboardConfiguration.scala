package com.ing.baker.http

import com.typesafe.config.Config

import scala.annotation.nowarn
import scala.collection.immutable.Map
import scala.collection.JavaConverters._

case class DashboardConfiguration(enabled: Boolean,
                                  applicationName: String,
                                  clusterInformation: Map[String, String])

object DashboardConfiguration {
  @nowarn
  def fromConfig(config: Config) : DashboardConfiguration = {
    val dashboardConfig = config.getConfig("baker.dashboard")
    val clusterInformation: Map[String, String] =
      dashboardConfig
        .getConfig("cluster-information")
        .entrySet().asScala
        .map(entry => (entry.getKey, entry.getValue.unwrapped().toString)).toMap

    DashboardConfiguration(
      enabled = dashboardConfig.getBoolean("enabled"),
      applicationName = dashboardConfig.getString("application-name"),
      clusterInformation = clusterInformation
    )
  }
}

