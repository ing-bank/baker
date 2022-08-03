package com.ing.baker.http

import java.net.URL
import scala.io.{BufferedSource, Source}
import scala.util.Try

object Dashboard {
  private val DASHBOARD_PREFIX = "dashboard_static/"

  /**
    * List of static files of the dashboard.
    */
  lazy val files : Seq[String] =
    Try(Source.fromResource("dashboard_static_index").getLines().map(_.replace(DASHBOARD_PREFIX, "")).toIndexedSeq)
      .getOrElse(throw new IllegalStateException("Expected list of dashboard files to be available under 'dashboard_static_index"))

  /**
    * Get URL to resource from filename. Do not specify the dashboard prefix, as it is automatically added.
    * Uses a whitelist of files to prevent any unauthorized access of resources by a malicious user.
    */
  def safeGetResourcePath(fileName: String) : Option[String] =
    files.find(_ == fileName).map(DASHBOARD_PREFIX + _)

  def dashboardConfigJson(apiPath: String, dashboardConfiguration: DashboardConfiguration) : String =
    s"""{
      |   "applicationName": "${dashboardConfiguration.applicationName}",
      |   "apiPath": "${apiPath}",
      |   "clusterInformation": {
      |   ${dashboardConfiguration.clusterInformation.map{ case (key, value) => s"""  "$key": "$value""""}.mkString(",\n     ")}
      |   }
      |}
      |""".stripMargin
}
