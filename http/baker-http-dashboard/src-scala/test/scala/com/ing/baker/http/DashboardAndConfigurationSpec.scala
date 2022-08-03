package com.ing.baker.http

import org.scalatest.flatspec._
import org.scalatest.matchers._

import scala.io.Source
import scala.util.Try


class DashboardAndConfigurationSpec extends AnyFlatSpec with should.Matchers {

  "The dashboard object" should "list the static files" in {
    Dashboard.files.find(_ == "index.html") should not be empty
  }

  "The safe get resource url" should "return a valid resource" in {
    val path = Dashboard.safeGetResourcePath("index.html")
    path should not be empty
    Try(Source.fromResource(path.get)).toOption should not be empty
  }

  "The versionJson" should "return a valid response" in {
    val configuration = DashboardConfiguration(
      enabled = true,
      applicationName = "application name",
      clusterInformation = Map(
        "version1" -> "1.0",
        "version2" -> "2.0"
      )
    )
    Dashboard.dashboardConfigJson("/test/path", configuration).replace(" ", "") shouldEqual
      """{
        |   "applicationName": "application name",
        |   "apiPath": "/test/path",
        |   "clusterInformation": {
        |     "version1": "1.0",
        |     "version2": "2.0"
        |   }
        | }
        |""".stripMargin.replace(" ", "")
  }


}
